/*
 * Thin Lean bindings to the agile API of OpenSSL (>= 3.2).
 *
 * Algorithms are given by their OpenSSL names (e.g. "SHA256", "AES-128-GCM", "ED25519", "P-256"),
 * chosen on the Lean side. This file only marshals arguments and calls OpenSSL.
 *
 * Every function is pure (deterministic) from Lean's point of view:
 * HPKE ephemeral keys are derived from caller-provided entropy,
 * and ECDSA uses deterministic nonces (RFC 6979).
 * Failures are reported as `none`; arguments are borrowed (`@&` in Lean).
 *
 * These bindings make no attempt at being side-channel resistant or at erasing secrets:
 * they are meant for testing and prototyping, not for production use.
 */

#include <lean/lean.h>
#include <string.h>
#include <openssl/opensslv.h>

#if OPENSSL_VERSION_NUMBER < 0x30200000L
#error "OpenSSL >= 3.2 is required (HPKE and deterministic ECDSA)"
#endif

#include <openssl/evp.h>
#include <openssl/kdf.h>
#include <openssl/core_names.h>
#include <openssl/hpke.h>
#include <openssl/ec.h>
#include <openssl/bn.h>
#include <openssl/param_build.h>

/* Lean helpers */

#define DATA(b) (lean_sarray_cptr((lean_object *)(b)))
#define SIZE(b) (lean_sarray_size(b))
#define STR(s) (lean_string_cstr(s))

static lean_obj_res mk_some(lean_obj_arg x) {
  lean_object *res = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(res, 0, x);
  return res;
}

static lean_obj_res mk_none(void) {
  return lean_box(0);
}

static lean_object *alloc_bytes(size_t len) {
  return lean_alloc_sarray(1, len, len);
}

/* Returns `some res` with its size truncated to `len`, or `none` (freeing `res`) if `!ok`. */
static lean_obj_res finish(int ok, lean_object *res, size_t len) {
  if (!ok) {
    lean_dec_ref(res);
    return mk_none();
  }
  lean_to_sarray(res)->m_size = len;
  return mk_some(res);
}

/* Hash */

LEAN_EXPORT lean_obj_res lean_openssl_digest(b_lean_obj_arg name, b_lean_obj_arg msg) {
  lean_object *res = alloc_bytes(EVP_MAX_MD_SIZE);
  size_t len = 0;
  int ok = EVP_Q_digest(NULL, STR(name), NULL, DATA(msg), SIZE(msg), DATA(res), &len) != 0;
  return finish(ok, res, len);
}

/* HMAC */

LEAN_EXPORT lean_obj_res lean_openssl_hmac(b_lean_obj_arg digest, b_lean_obj_arg key, b_lean_obj_arg data) {
  lean_object *res = alloc_bytes(EVP_MAX_MD_SIZE);
  size_t len = 0;
  int ok = EVP_Q_mac(NULL, "HMAC", NULL, STR(digest), NULL, DATA(key), SIZE(key), DATA(data), SIZE(data),
                     DATA(res), EVP_MAX_MD_SIZE, &len) != NULL;
  return finish(ok, res, len);
}

/* HKDF (RFC 5869) */

static lean_obj_res hkdf(int mode, b_lean_obj_arg digest, b_lean_obj_arg key,
                         const char *salt_or_info_name, b_lean_obj_arg salt_or_info, size_t len) {
  EVP_KDF *kdf = EVP_KDF_fetch(NULL, "HKDF", NULL);
  EVP_KDF_CTX *ctx = kdf != NULL ? EVP_KDF_CTX_new(kdf) : NULL;
  EVP_KDF_free(kdf);
  OSSL_PARAM params[] = {
    OSSL_PARAM_construct_int(OSSL_KDF_PARAM_MODE, &mode),
    OSSL_PARAM_construct_utf8_string(OSSL_KDF_PARAM_DIGEST, (char *)STR(digest), 0),
    OSSL_PARAM_construct_octet_string(OSSL_KDF_PARAM_KEY, DATA(key), SIZE(key)),
    OSSL_PARAM_construct_octet_string(salt_or_info_name, DATA(salt_or_info), SIZE(salt_or_info)),
    OSSL_PARAM_construct_end(),
  };
  lean_object *res = alloc_bytes(len);
  int ok = ctx != NULL && (len == 0 || EVP_KDF_derive(ctx, DATA(res), len, params) > 0);
  EVP_KDF_CTX_free(ctx);
  return finish(ok, res, len);
}

/* HKDF-Extract(salt, ikm); `len` must be the output length of `digest`. */
LEAN_EXPORT lean_obj_res lean_openssl_hkdf_extract(b_lean_obj_arg digest, b_lean_obj_arg salt, b_lean_obj_arg ikm,
                                                   size_t len) {
  return hkdf(EVP_KDF_HKDF_MODE_EXTRACT_ONLY, digest, ikm, OSSL_KDF_PARAM_SALT, salt, len);
}

/* HKDF-Expand(prk, info, len) */
LEAN_EXPORT lean_obj_res lean_openssl_hkdf_expand(b_lean_obj_arg digest, b_lean_obj_arg prk, b_lean_obj_arg info,
                                                  size_t len) {
  return hkdf(EVP_KDF_HKDF_MODE_EXPAND_ONLY, digest, prk, OSSL_KDF_PARAM_INFO, info, len);
}

/* AEAD, with the tag (of length `tag_len`) appended to the ciphertext */

LEAN_EXPORT lean_obj_res lean_openssl_aead_encrypt(b_lean_obj_arg cipher_name, size_t tag_len,
                                                   b_lean_obj_arg key, b_lean_obj_arg nonce,
                                                   b_lean_obj_arg ad, b_lean_obj_arg pt) {
  EVP_CIPHER *cipher = EVP_CIPHER_fetch(NULL, STR(cipher_name), NULL);
  EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
  size_t nonce_len = SIZE(nonce);
  OSSL_PARAM params[] = {
    OSSL_PARAM_construct_size_t(OSSL_CIPHER_PARAM_AEAD_IVLEN, &nonce_len),
    OSSL_PARAM_construct_end(),
  };
  size_t ct_len = SIZE(pt) + tag_len;
  lean_object *res = alloc_bytes(ct_len);
  unsigned char *out = DATA(res);
  int len = 0;
  int ok = cipher != NULL && ctx != NULL
    && (size_t)EVP_CIPHER_get_key_length(cipher) == SIZE(key)
    && EVP_EncryptInit_ex2(ctx, cipher, NULL, NULL, params)
    && EVP_EncryptInit_ex2(ctx, NULL, DATA(key), DATA(nonce), NULL)
    && EVP_EncryptUpdate(ctx, NULL, &len, DATA(ad), (int)SIZE(ad))
    && EVP_EncryptUpdate(ctx, out, &len, DATA(pt), (int)SIZE(pt))
    && EVP_EncryptFinal_ex(ctx, out + len, &len)
    && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, (int)tag_len, out + SIZE(pt));
  EVP_CIPHER_CTX_free(ctx);
  EVP_CIPHER_free(cipher);
  return finish(ok, res, ct_len);
}

LEAN_EXPORT lean_obj_res lean_openssl_aead_decrypt(b_lean_obj_arg cipher_name, size_t tag_len,
                                                   b_lean_obj_arg key, b_lean_obj_arg nonce,
                                                   b_lean_obj_arg ad, b_lean_obj_arg ct) {
  if (SIZE(ct) < tag_len) return mk_none();
  EVP_CIPHER *cipher = EVP_CIPHER_fetch(NULL, STR(cipher_name), NULL);
  EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
  size_t nonce_len = SIZE(nonce);
  OSSL_PARAM params[] = {
    OSSL_PARAM_construct_size_t(OSSL_CIPHER_PARAM_AEAD_IVLEN, &nonce_len),
    OSSL_PARAM_construct_end(),
  };
  size_t pt_len = SIZE(ct) - tag_len;
  lean_object *res = alloc_bytes(pt_len);
  unsigned char *out = DATA(res);
  int len = 0;
  int ok = cipher != NULL && ctx != NULL
    && (size_t)EVP_CIPHER_get_key_length(cipher) == SIZE(key)
    && EVP_DecryptInit_ex2(ctx, cipher, NULL, NULL, params)
    && EVP_DecryptInit_ex2(ctx, NULL, DATA(key), DATA(nonce), NULL)
    && EVP_DecryptUpdate(ctx, NULL, &len, DATA(ad), (int)SIZE(ad))
    && EVP_DecryptUpdate(ctx, out, &len, DATA(ct), (int)pt_len)
    && EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, (int)tag_len, DATA(ct) + pt_len)
    && EVP_DecryptFinal_ex(ctx, out + len, &len) > 0;
  EVP_CIPHER_CTX_free(ctx);
  EVP_CIPHER_free(cipher);
  return finish(ok, res, pt_len);
}

/* Keys
 *
 * `key_type` is an OpenSSL key type name ("ED25519", "ED448", "X25519", "X448", or "EC").
 * For "EC", `group` is the curve name ("P-256", ...), private keys are big-endian scalars,
 * and public keys are uncompressed points. Otherwise, keys are raw and `group` is ignored.
 */

static int is_ec(b_lean_obj_arg key_type) {
  return strcmp(STR(key_type), "EC") == 0;
}

/* EC key pair from a private scalar: OpenSSL does not compute the public point on import. */
static EVP_PKEY *ec_private_key(const char *group_name, b_lean_obj_arg sk) {
  EVP_PKEY *pkey = NULL;
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
  OSSL_PARAM_BLD *bld = OSSL_PARAM_BLD_new();
  BIGNUM *priv = BN_bin2bn(DATA(sk), (int)SIZE(sk), NULL);
  EC_GROUP *group = EC_GROUP_new_by_curve_name_ex(NULL, NULL, EC_curve_nist2nid(group_name));
  EC_POINT *point = group != NULL ? EC_POINT_new(group) : NULL;
  unsigned char pub[256];
  size_t pub_len = 0;
  OSSL_PARAM *params = NULL;
  int ok = ctx != NULL && bld != NULL && priv != NULL && point != NULL
    && EC_POINT_mul(group, point, priv, NULL, NULL, NULL)
    && (pub_len = EC_POINT_point2oct(group, point, POINT_CONVERSION_UNCOMPRESSED, pub, sizeof(pub), NULL)) != 0
    && OSSL_PARAM_BLD_push_utf8_string(bld, OSSL_PKEY_PARAM_GROUP_NAME, group_name, 0)
    && OSSL_PARAM_BLD_push_octet_string(bld, OSSL_PKEY_PARAM_PUB_KEY, pub, pub_len)
    && OSSL_PARAM_BLD_push_BN(bld, OSSL_PKEY_PARAM_PRIV_KEY, priv)
    && (params = OSSL_PARAM_BLD_to_param(bld)) != NULL
    && EVP_PKEY_fromdata_init(ctx) > 0;
  if (ok && EVP_PKEY_fromdata(ctx, &pkey, EVP_PKEY_KEYPAIR, params) <= 0) pkey = NULL;
  OSSL_PARAM_free(params);
  EC_POINT_free(point);
  EC_GROUP_free(group);
  BN_clear_free(priv);
  OSSL_PARAM_BLD_free(bld);
  EVP_PKEY_CTX_free(ctx);
  return pkey;
}

static EVP_PKEY *private_key(b_lean_obj_arg key_type, b_lean_obj_arg group, b_lean_obj_arg sk) {
  if (is_ec(key_type)) return ec_private_key(STR(group), sk);
  return EVP_PKEY_new_raw_private_key_ex(NULL, STR(key_type), NULL, DATA(sk), SIZE(sk));
}

static EVP_PKEY *public_key(b_lean_obj_arg key_type, b_lean_obj_arg group, b_lean_obj_arg pk) {
  if (!is_ec(key_type)) return EVP_PKEY_new_raw_public_key_ex(NULL, STR(key_type), NULL, DATA(pk), SIZE(pk));
  EVP_PKEY *pkey = NULL;
  EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
  OSSL_PARAM params[] = {
    OSSL_PARAM_construct_utf8_string(OSSL_PKEY_PARAM_GROUP_NAME, (char *)STR(group), 0),
    OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_PUB_KEY, DATA(pk), SIZE(pk)),
    OSSL_PARAM_construct_end(),
  };
  if (ctx == NULL || EVP_PKEY_fromdata_init(ctx) <= 0 || EVP_PKEY_fromdata(ctx, &pkey, EVP_PKEY_PUBLIC_KEY, params) <= 0)
    pkey = NULL;
  EVP_PKEY_CTX_free(ctx);
  return pkey;
}

LEAN_EXPORT lean_obj_res lean_openssl_secret_to_public(b_lean_obj_arg key_type, b_lean_obj_arg group,
                                                       b_lean_obj_arg sk) {
  EVP_PKEY *pkey = private_key(key_type, group, sk);
  lean_object *res = alloc_bytes(256);
  size_t len = 256;
  int ok = pkey != NULL && (is_ec(key_type)
    ? EVP_PKEY_get_octet_string_param(pkey, OSSL_PKEY_PARAM_PUB_KEY, DATA(res), len, &len)
    : EVP_PKEY_get_raw_public_key(pkey, DATA(res), &len));
  EVP_PKEY_free(pkey);
  return finish(ok, res, len);
}

/* Signatures
 *
 * `digest` is the name of the hash function ("" for EdDSA, which hashes internally).
 * ECDSA uses deterministic nonces (RFC 6979) and DER-encoded signatures.
 */

LEAN_EXPORT lean_obj_res lean_openssl_sign(b_lean_obj_arg key_type, b_lean_obj_arg group, b_lean_obj_arg digest,
                                           b_lean_obj_arg sk, b_lean_obj_arg msg) {
  EVP_PKEY *pkey = private_key(key_type, group, sk);
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  unsigned int nonce_type = 1;
  OSSL_PARAM params[] = {
    OSSL_PARAM_construct_uint(OSSL_SIGNATURE_PARAM_NONCE_TYPE, &nonce_type),
    OSSL_PARAM_construct_end(),
  };
  const char *md = lean_string_size(digest) > 1 ? STR(digest) : NULL; /* the size includes the final NUL */
  size_t len = 0;
  lean_object *res = alloc_bytes(0);
  int ok = pkey != NULL && ctx != NULL
    && EVP_DigestSignInit_ex(ctx, NULL, md, NULL, NULL, pkey, is_ec(key_type) ? params : NULL) > 0
    && EVP_DigestSign(ctx, NULL, &len, DATA(msg), SIZE(msg)) > 0;
  if (ok) {
    lean_dec_ref(res);
    res = alloc_bytes(len);
    ok = EVP_DigestSign(ctx, DATA(res), &len, DATA(msg), SIZE(msg)) > 0;
  }
  EVP_MD_CTX_free(ctx);
  EVP_PKEY_free(pkey);
  return finish(ok, res, len);
}

LEAN_EXPORT uint8_t lean_openssl_verify(b_lean_obj_arg key_type, b_lean_obj_arg group, b_lean_obj_arg digest,
                                        b_lean_obj_arg pk, b_lean_obj_arg msg, b_lean_obj_arg sig) {
  EVP_PKEY *pkey = public_key(key_type, group, pk);
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  const char *md = lean_string_size(digest) > 1 ? STR(digest) : NULL;
  int ok = pkey != NULL && ctx != NULL
    && EVP_DigestVerifyInit_ex(ctx, NULL, md, NULL, NULL, pkey, NULL) > 0
    && EVP_DigestVerify(ctx, DATA(sig), SIZE(sig), DATA(msg), SIZE(msg)) == 1;
  EVP_MD_CTX_free(ctx);
  EVP_PKEY_free(pkey);
  return ok;
}

/* HPKE (RFC 9180), base mode. Algorithms are given by their RFC 9180 identifiers. */

/* DeriveKeyPair(ikm): returns sk ++ pk, where `sk_len` is the length of a serialized private key. */
LEAN_EXPORT lean_obj_res lean_openssl_hpke_derive_key_pair(uint16_t kem, uint16_t kdf, uint16_t aead,
                                                           b_lean_obj_arg key_type, size_t sk_len, b_lean_obj_arg ikm) {
  OSSL_HPKE_SUITE suite = { kem, kdf, aead };
  size_t pk_len = OSSL_HPKE_get_public_encap_size(suite);
  lean_object *res = alloc_bytes(sk_len + pk_len);
  EVP_PKEY *priv = NULL;
  BIGNUM *bn = NULL;
  size_t len = sk_len;
  int ok = OSSL_HPKE_keygen(suite, DATA(res) + sk_len, &pk_len, &priv, DATA(ikm), SIZE(ikm), NULL, NULL) == 1
    && (is_ec(key_type)
      ? EVP_PKEY_get_bn_param(priv, OSSL_PKEY_PARAM_PRIV_KEY, &bn) && BN_bn2binpad(bn, DATA(res), (int)sk_len) == (int)sk_len
      : EVP_PKEY_get_raw_private_key(priv, DATA(res), &len) && len == sk_len);
  BN_clear_free(bn);
  EVP_PKEY_free(priv);
  return finish(ok, res, sk_len + pk_len);
}

/* SealBase, with the ephemeral key pair derived from `ikme` by DeriveKeyPair: returns enc ++ ciphertext. */
LEAN_EXPORT lean_obj_res lean_openssl_hpke_seal_base(uint16_t kem, uint16_t kdf, uint16_t aead,
                                                     b_lean_obj_arg pk_r, b_lean_obj_arg info,
                                                     b_lean_obj_arg ad, b_lean_obj_arg pt, b_lean_obj_arg ikme) {
  OSSL_HPKE_SUITE suite = { kem, kdf, aead };
  OSSL_HPKE_CTX *ctx = OSSL_HPKE_CTX_new(OSSL_HPKE_MODE_BASE, suite, OSSL_HPKE_ROLE_SENDER, NULL, NULL);
  size_t enc_len = OSSL_HPKE_get_public_encap_size(suite);
  size_t ct_len = OSSL_HPKE_get_ciphertext_size(suite, SIZE(pt));
  size_t out_len = enc_len + ct_len;
  lean_object *res = alloc_bytes(out_len);
  int ok = ctx != NULL
    && OSSL_HPKE_CTX_set1_ikme(ctx, DATA(ikme), SIZE(ikme)) == 1
    && OSSL_HPKE_encap(ctx, DATA(res), &enc_len, DATA(pk_r), SIZE(pk_r), DATA(info), SIZE(info)) == 1
    && OSSL_HPKE_seal(ctx, DATA(res) + enc_len, &ct_len, DATA(ad), SIZE(ad), DATA(pt), SIZE(pt)) == 1;
  OSSL_HPKE_CTX_free(ctx);
  return finish(ok, res, enc_len + ct_len);
}

LEAN_EXPORT lean_obj_res lean_openssl_hpke_open_base(uint16_t kem, uint16_t kdf, uint16_t aead,
                                                     b_lean_obj_arg key_type, b_lean_obj_arg group,
                                                     b_lean_obj_arg enc, b_lean_obj_arg sk_r,
                                                     b_lean_obj_arg info, b_lean_obj_arg ad, b_lean_obj_arg ct) {
  OSSL_HPKE_SUITE suite = { kem, kdf, aead };
  EVP_PKEY *priv = private_key(key_type, group, sk_r);
  OSSL_HPKE_CTX *ctx = OSSL_HPKE_CTX_new(OSSL_HPKE_MODE_BASE, suite, OSSL_HPKE_ROLE_RECEIVER, NULL, NULL);
  size_t pt_len = SIZE(ct);
  lean_object *res = alloc_bytes(pt_len);
  int ok = priv != NULL && ctx != NULL
    && OSSL_HPKE_decap(ctx, DATA(enc), SIZE(enc), priv, DATA(info), SIZE(info)) == 1
    && OSSL_HPKE_open(ctx, DATA(res), &pt_len, DATA(ad), SIZE(ad), DATA(ct), SIZE(ct)) == 1;
  OSSL_HPKE_CTX_free(ctx);
  EVP_PKEY_free(priv);
  return finish(ok, res, pt_len);
}
