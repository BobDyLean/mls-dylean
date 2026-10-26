module

public import MLS.TreeSync.Symbolic.API
public import MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
public import MLS.Bootstrap.Symbolic.KeyPackage
public import MLS.Bootstrap.Symbolic.State.KeyPackageStore
public import MLS.TreeKEM.Symbolic.State.API
public import MLS.TreeKEM.Symbolic.State.PSKStore
public import MLS.TreeKEM.Symbolic.State.ProposalCache
public import MLS.TreeKEM.Symbolic.State.UpdateCache
public import MLS.TreeKEM.Symbolic.EpochEvent
public import DY.Actions.Network

/-!
The trace entries used by the traceful functions of TreeKEM (`MLS.TreeKEM.Symbolic.Traceful.*`),
bundled in a typeclass whose fields are scoped instances in the namespace `MLS.TreeKEM`
(the TreeSync ones are in `HasTreeSyncExecTrace tkt`).
The top-level protocol provides it after combining the corresponding trace entries
(`instance: HasTreeKEMExecTrace where`).
-/

namespace MLS.TreeKEM

open DY
open MLS MLS.TreeSync MLS.Bootstrap
open DySlop.Map (Map)

public
class HasTreeKEMExecTrace [HasSymbolicBytes] [ExecTraceTypes] where
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMNodeKeysState)]
  [traceExec2: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT TreeKEMEpochSecret)]
  [traceExec3: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BareTreeSyncTreeKEMState)]
  [traceExec4: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT OnePskState)]
  [traceExec5: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (Map PskStoreKey PskStoreValue))]
  [traceExec6: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (Map ProposalCacheKey ProposalAndSender))]
  [traceExec7: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT (Map UpdateCacheKey UpdateCacheValue))]
  [traceExec8: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT BootstrapInitKeyState)]
  [traceExec9: ExecTraceTypes.Has (PersistentLocalState.CompromisableState.ExecEntryT KeyPackageStorePre)]
  [traceExec10: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT IAmInGroup)]
  [traceExec11: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT KeyPackageHasBeenVerified)]
  [traceExec12: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT (LeafNodeHasBeenVerified tkt))]

attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec0
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec1
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec2
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec3
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec4
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec5
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec6
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec7
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec8
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec9
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec10
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec11
attribute [reducible, scoped instance] HasTreeKEMExecTrace.traceExec12

end MLS.TreeKEM
