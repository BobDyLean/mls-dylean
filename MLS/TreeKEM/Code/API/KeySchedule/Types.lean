module

/-!
Port of `MLS.TreeKEM.API.KeySchedule.Types`.
-/

namespace MLS.TreeKEM

/--
Port of `epoch_keys`.
All the keys that are not forward-secret within an epoch.
In particular, encryption_secret is not in this set of keys:
it is returned by the commit function
-/
public
structure EpochKeys (Bytes: Type) where
  senderDataSecret: Bytes
  exporterSecret: Bytes
  externalSecret: Bytes
  membershipKey: Bytes
  resumptionPsk: Bytes
  epochAuthenticator: Bytes
  confirmationTag: Bytes

/-- Port of `treekem_keyschedule_state`. -/
public
structure TreeKEMKeyscheduleState (Bytes: Type) where
  epochKeys: EpochKeys Bytes
  initSecret: Bytes

end MLS.TreeKEM
