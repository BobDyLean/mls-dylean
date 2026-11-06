module

public import OpenSSL

/-!
Tests of the OpenSSL bindings.
Each primitive is checked against published test vectors where available.
-/

namespace OpenSSL.Test

open OpenSSL

public
def hexDigit (c: Char): Except String UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10).toUInt8
  else throw s!"invalid hex digit {c}"

public
def fromHex (s: String): IO ByteArray := do
  let rec go: List Char → Except String (List UInt8)
    | [] => pure []
    | [_] => throw "odd length"
    | h1::h2::t => do pure ((16 * (← hexDigit h1) + (← hexDigit h2))::(← go t))
  match go s.toList with
  | .ok l => pure ⟨l.toArray⟩
  | .error e => throw (IO.userError e)

public
def toHex (b: ByteArray): String :=
  let d (n: Nat): Char := if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)
  String.ofList (b.toList.flatMap fun x => [d (x.toNat / 16), d (x.toNat % 16)])

public
def bytes (n: Nat) (seed: Nat): ByteArray :=
  ⟨((List.range n).map fun i => ((i * 7 + seed * 13 + 1) % 256).toUInt8).toArray⟩

public
def fail {α: Type} (msg: String): IO α := throw (IO.userError msg)

public
def expectSome {α: Type} (name: String) (x: Option α): IO α :=
  match x with
  | some x => pure x
  | none => fail s!"{name}: failed"

public
def expectEq (name: String) (expected: String) (got: ByteArray): IO Unit :=
  if expected != toHex got then fail s!"{name}: expected {expected}, got {toHex got}" else pure ()

/-! ## Hash, HMAC, HKDF -/

/-- FIPS 180-2, "abc". -/
public
def testHash: IO Unit := do
  let msg := "abc".toUTF8
  expectEq "SHA256" "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    (← expectSome "SHA256" (Hash.hash .sha2_256 msg))
  expectEq "SHA384" "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
    (← expectSome "SHA384" (Hash.hash .sha2_384 msg))
  expectEq "SHA512" "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    (← expectSome "SHA512" (Hash.hash .sha2_512 msg))

/-- RFC 4231, test case 2. -/
public
def testHmac: IO Unit := do
  let key := "Jefe".toUTF8
  let data := "what do ya want for nothing?".toUTF8
  expectEq "HMAC-SHA256" "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    (← expectSome "HMAC-SHA256" (Hash.hmac .sha2_256 key data))
  expectEq "HMAC-SHA384" "af45d2e376484031617f78d2b58a6b1b9c7ef464f5a01b47e42ec3736322445e8e2240ca5e69e2c78b3239ecfab21649"
    (← expectSome "HMAC-SHA384" (Hash.hmac .sha2_384 key data))
  expectEq "HMAC-SHA512" "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"
    (← expectSome "HMAC-SHA512" (Hash.hmac .sha2_512 key data))

/-- RFC 5869, test case 1. -/
public
def testHkdf: IO Unit := do
  let ikm ← fromHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
  let salt ← fromHex "000102030405060708090a0b0c"
  let info ← fromHex "f0f1f2f3f4f5f6f7f8f9"
  let prk ← expectSome "HKDF-SHA256-Extract" (Hash.hkdfExtract .sha2_256 salt ikm)
  expectEq "HKDF-SHA256-Extract" "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5" prk
  expectEq "HKDF-SHA256-Expand" "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
    (← expectSome "HKDF-SHA256-Expand" (Hash.hkdfExpand .sha2_256 prk info 42))
  -- SHA-384 / SHA-512: output lengths, and Expand(Extract) is consistent with the requested length
  let prk384 ← expectSome "HKDF-SHA384-Extract" (Hash.hkdfExtract .sha2_384 salt ikm)
  let prk512 ← expectSome "HKDF-SHA512-Extract" (Hash.hkdfExtract .sha2_512 salt ikm)
  if prk384.size != Hash.Algorithm.sha2_384.hashLength || prk512.size != Hash.Algorithm.sha2_512.hashLength then
    fail "HKDF-Extract: wrong output length"
  if (← expectSome "HKDF-SHA384-Expand" (Hash.hkdfExpand .sha2_384 prk384 info 100)).size != 100 then
    fail "HKDF-SHA384-Expand: wrong output length"
  if (← expectSome "HKDF-SHA512-Expand" (Hash.hkdfExpand .sha2_512 prk512 info 100)).size != 100 then
    fail "HKDF-SHA512-Expand: wrong output length"

/-! ## AEAD -/

/-- RFC 8439 Section 2.8.2, and round trips for every AEAD. -/
public
def testAead: IO Unit := do
  let key ← fromHex "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let nonce ← fromHex "070000004041424344454647"
  let ad ← fromHex "50515253c0c1c2c3c4c5c6c7"
  let plaintext := "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.".toUTF8
  expectEq "ChaCha20Poly1305"
    ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116"
      ++ "1ae10b594f09e26a7e902ecbd0600691")
    (← expectSome "ChaCha20Poly1305" (AEAD.encrypt .chacha20Poly1305 key nonce ad plaintext))
  for a in [AEAD.Algorithm.aes128Gcm, .aes256Gcm, .chacha20Poly1305] do
    let name := s!"{repr a}"
    let key := key.extract 0 a.keyLength
    let ct ← expectSome s!"{name}.encrypt" (AEAD.encrypt a key nonce ad plaintext)
    expectEq s!"{name} round trip" (toHex plaintext) (← expectSome s!"{name}.decrypt" (AEAD.decrypt a key nonce ad ct))
    let tampered := ct.set! 0 (ct.get! 0 ^^^ 1)
    if (AEAD.decrypt a key nonce ad tampered).isSome then fail s!"{name}: accepted a tampered ciphertext"
    if (AEAD.encrypt a (key.extract 0 (a.keyLength - 1)) nonce ad plaintext).isSome then fail s!"{name}: accepted a short key"
    if (AEAD.encrypt a key (nonce.extract 0 11) ad plaintext).isSome then fail s!"{name}: accepted a short nonce"

/-! ## Signatures -/

/-- RFC 8032, Section 7.1 TEST 1 and Section 7.4 "Blank". -/
public
def testEdDSA: IO Unit := do
  for (a, sk, pk, sig) in [
    (Signature.Algorithm.ed25519,
      "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
      "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
      "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"),
    (.ed448,
      "6c82a562cb808d10d632be89c8513ebf6c929f34ddfa8c9f63c9960ef6e348a3528c8a3fcc2f044e39a3fc5b94492f8f032e7549a20098f95b",
      "5fd7449b59b461fd2ce787ec616ad46a1da1342485a70e1f8a0ea75d80e96778edf124769b46c7061bd6783df1e50f6cd1fa1abeafe8256180",
      "533a37f6bbe457251f023c0d88f976ae2dfb504a843e34d2074fd823d41a591f2b233f034f628281f2fd7a22ddd47d7828c59bd0a21bfd3980ff0d2028d4b18a9df63e006c5d1c2d345b925d8dc00b4104852db99ac5c7cdda8530a113a0f4dbb61149f05a7363268c71d95808ff2e652600")
  ] do
    let name := s!"{repr a}"
    let sk ← fromHex sk
    let myPk ← expectSome s!"{name}.secretToPublic" (Signature.secretToPublic a sk)
    expectEq s!"{name}.secretToPublic" pk myPk
    let mySig ← expectSome s!"{name}.sign" (Signature.sign a sk .empty)
    expectEq s!"{name}.sign" sig mySig
    if !Signature.verify a myPk .empty mySig then fail s!"{name}.verify: rejected a valid signature"
    if Signature.verify a myPk "x".toUTF8 mySig then fail s!"{name}.verify: accepted a wrong message"

/-- Round trips: signatures are deterministic, verify, and are bound to the message and curve. -/
public
def testECDSA: IO Unit := do
  let msg := "abc".toUTF8
  for a in [Signature.Algorithm.ecdsaP256Sha256, .ecdsaP384Sha384, .ecdsaP521Sha512] do
    let name := s!"{repr a}"
    let sk := bytes a.secretKeyLength 1
    let pk ← expectSome s!"{name}.secretToPublic" (Signature.secretToPublic a sk)
    if pk.size != a.publicKeyLength then fail s!"{name}.secretToPublic: wrong length"
    let sig1 ← expectSome s!"{name}.sign" (Signature.sign a sk msg)
    let sig2 ← expectSome s!"{name}.sign" (Signature.sign a sk msg)
    expectEq s!"{name}.sign determinism" (toHex sig1) sig2
    if !Signature.verify a pk msg sig1 then fail s!"{name}.verify: rejected a valid signature"
    if Signature.verify a pk "abd".toUTF8 sig1 then fail s!"{name}.verify: accepted a wrong message"
  -- A P-256 signature does not verify under P-384
  let sig ← expectSome "P-256 sign" (Signature.sign .ecdsaP256Sha256 (bytes 32 1) msg)
  let pk384 ← expectSome "P-384 secretToPublic" (Signature.secretToPublic .ecdsaP384Sha384 (bytes 48 1))
  if Signature.verify .ecdsaP384Sha384 pk384 msg sig then fail "ECDSA: P-256 signature accepted under P-384"

/-! ## HPKE -/

/-- Known-answer tests (generated with OpenSSL 3.6), and round trips. -/
public
def hpkeKats: List (HPKE.Ciphersuite × String × String × String × String) := [
    ({ kem := .dhkemX25519HkdfSha256, kdf := .hkdfSha256, aead := .aes128Gcm }, "b8e91e922013c353d6414276c55589cd51058de93d32d929ab08a0116b5fce6b", "281d5103421a9feb158160a1e1d1d5c598229773c32f12b63a697f13f9416e21", "55ca7f6687c39855491be0865d7d6359e2f4c0a3de509a9e5ae8de2397860979", "2ad75c21f5e594ecff0a4ab0798ad93816d7f1e74be2d6e4c655f813e5bce99d5045b5b4d66c46d44606973bbbd2"),
    ({ kem := .dhkemP256HkdfSha256, kdf := .hkdfSha256, aead := .aes128Gcm }, "d6ec5c9c3b2587fb421e400dffa8a6b71e5a77b12ed6091ed8bd1ba8077156a8", "042bffae0a4abc687cf2c2940d3d8a1c3e4bd7946315f3e04272fc7f58c44597527f2e7cd0a1c0351f9b109282c3aba2dac99e3390ff0a4ea312b26b0a87802a00", "0496b0478d795b66c3d40da0a30d81e066b5b5c3be9186948092ffc022ee94ec8668f257b9d56b9a516ea6e21552f6443b0eb9a0fbf69640d86dfb0602b1406225", "16a0e0d832a41ec68e2bc2c58660ceaff680b4a3df0c7eb531033ab366d0b0b7569c633101716d14d3c56646d7ea"),
    ({ kem := .dhkemX25519HkdfSha256, kdf := .hkdfSha256, aead := .chacha20Poly1305 }, "b8e91e922013c353d6414276c55589cd51058de93d32d929ab08a0116b5fce6b", "281d5103421a9feb158160a1e1d1d5c598229773c32f12b63a697f13f9416e21", "55ca7f6687c39855491be0865d7d6359e2f4c0a3de509a9e5ae8de2397860979", "354c9442883ed55ceb066cb31d13b0142e234de6093bd01d21f86d088368aac838fbd33e59ba3334222bbb79f9d8"),
    ({ kem := .dhkemX448HkdfSha512, kdf := .hkdfSha512, aead := .aes256Gcm }, "0852d0a73097514c2ee03d48db402dff26fccac04d9ab0c463250c0f3693527358c11659bb2f1f6043de87667c4d88049c2576f8ee30b58f", "d671e957385951cb1ff9ed710097b7ade6de107c4fbcc6d4fc37fc33d3636b1c61bb56463a7b6c789153efbbcf9dadf2cc8b263bd4a8cd32", "b7315b144e2f3bd0ddc1dca0f2a7c5639c4e84408a392fabc5f4889d19c58d5be4273dd92c98149d5f418f7dc31b7ca27a81896b3acccd16", "5ba038da3330e3446654c69b40bbfff19aed7593bc5be70182fb89be7691a83826ce05d8410290d3ad7fcf7ad9ab"),
    ({ kem := .dhkemP521HkdfSha512, kdf := .hkdfSha512, aead := .aes256Gcm }, "00e8e98d9be6973cd4407680d9d28ab80c4aa11581dd857c92bee0af780a1ef1c80cf8cc0517e77f8c1c2fa6cb8e047cf2f6bcdcc5c396041c1afec20ee5c8180a12", "0400a4d38a77aa77afdb4c2e3aa891a164ac85073f8d515b3e937c057de909e1c8487e825f13d8f9e19e6c27dbf06d6905b07c465adcd50a72c632686e32704dc1edd501c5ebaac8bdd6fbc35775a41640cc45634fe414a0bbe36c2ba2b6e5b07318297abf20e8a6eeabe1dbacbc1963dd1361f376ec4a15d22dabf807153227c7e8cd49c5", "04008bbd184a021a3dcd4137de0de5a8971f8c5e92f08dac680e4750ab79797d4f04756f2c8ca309ae1272b29a398d200d96a2f7e26bcaff682adbce48e17800e14a4a01698b27dde2973604a6872fb55f4d20ec2ab653224c09ad57a8eeb9aeef6ccdf17af7d3118dec3dbd415b754e039eb2d6e5ba763f739fa824521c59f06ac4830677", "5fc7e134359ba8b9f0d044dd198cf993d8490b0659abea32517f06200cc4762b485aac9f890ebcba91ffd25cacb6"),
    ({ kem := .dhkemX448HkdfSha512, kdf := .hkdfSha512, aead := .chacha20Poly1305 }, "0852d0a73097514c2ee03d48db402dff26fccac04d9ab0c463250c0f3693527358c11659bb2f1f6043de87667c4d88049c2576f8ee30b58f", "d671e957385951cb1ff9ed710097b7ade6de107c4fbcc6d4fc37fc33d3636b1c61bb56463a7b6c789153efbbcf9dadf2cc8b263bd4a8cd32", "b7315b144e2f3bd0ddc1dca0f2a7c5639c4e84408a392fabc5f4889d19c58d5be4273dd92c98149d5f418f7dc31b7ca27a81896b3acccd16", "c8f35338714405c84f150101c650f659993e1e8dccf16e99793f00f253c51bd7583bc1a268d96cda58562998930f"),
    ({ kem := .dhkemP384HkdfSha384, kdf := .hkdfSha384, aead := .aes256Gcm }, "6a9f6b6c83e92663c3a60c5d46273d0f8314504ec2c69b5908dd1f57c90b7adc3bcae87d3fc592a574fccc53aa0875a6", "04f3ad4ffc193aeceddfb05afd3408823609601fa6a23679ea1697d13d81e32a44d0a95d308fa12927f17912f0ef9b3a5bac1241d864b5375c99527247e8c4abe7bd1876b7437cf49a5dd25d49ba734499fbd18c755caae3f44ebfb40db76ec9f3", "04c49e5b7004172bff834791cdc3a56da624569cc5543a669faabbd1395bf6891a802d71e0588b9778917b64e0cf1a6100a01a1acee669dfa00add37da6651933325b095302839ee992fd9cd516fb051e4d66ee3ce72aabc8969ac8a9f07073207", "4ae8bb69c8d7e34a8a4cf33390e3393e82a203c5095d244bbc6f3893cd90d83cec8e689ae0e1a2caae873a11d443")
]

public
def testHpke: IO Unit := do
  for (cs, skR, pkR, enc, ct) in hpkeKats do
    let name := s!"HPKE {repr cs}"
    let (mySkR, myPkR) ← expectSome s!"{name}.deriveKeyPair" (HPKE.deriveKeyPair cs (bytes 66 1))
    expectEq s!"{name}.deriveKeyPair sk" skR mySkR
    expectEq s!"{name}.deriveKeyPair pk" pkR myPkR
    let info := bytes 20 3
    let ad := bytes 10 4
    let plaintext := bytes 30 5
    let (myEnc, myCt) ← expectSome s!"{name}.sealBase" (HPKE.sealBase cs myPkR info ad plaintext (bytes 66 2))
    expectEq s!"{name}.sealBase enc" enc myEnc
    expectEq s!"{name}.sealBase ciphertext" ct myCt
    let pt ← expectSome s!"{name}.openBase" (HPKE.openBase cs myEnc mySkR info ad myCt)
    expectEq s!"{name}.openBase" (toHex plaintext) pt
    if (HPKE.openBase cs myEnc mySkR (bytes 20 9) ad myCt).isSome then
      fail s!"{name}.openBase: accepted a wrong info"

public
def main: IO Unit := do
  testHash
  testHmac
  testHkdf
  testAead
  testEdDSA
  testECDSA
  testHpke
  IO.println "OpenSSL bindings: all tests passed"

end OpenSSL.Test
