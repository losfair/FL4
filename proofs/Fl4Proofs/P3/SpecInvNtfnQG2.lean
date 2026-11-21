/-
P3 (DESIGN.md §9), invariant line G1 (nq2, nq3): **the functions that may
block a thread of `K` on an endpoint** — `send_ipc`, `send_fault_ipc`,
`handle_timeout`, `handle_fault`, `receive_ipc`, `do_reply_transfer`,
`invoke_tcb` (spec side only). Their posts drop only the thread that may
block (`NQ (K.filter (· ≠ t))`), so a thread of `K` other than it stays in
`K`.

nq3: hand-written (no longer generated); each function is split per match arm /
`if` branch into small pre/post steps (the `do` blocks' join points made the
whole-body unifications of nq2's `nqh_auto` time out).
* `nq_sendIpc` (post: the sender leaves `K`), `nq_sendIpc_nb` (non-blocking:
  `NQK K`).
* `nq_receiveIpc`: the reply-cap prefix, the endpoint / notification reads as
  IK steps; the `complete_signal` arm, the sender arm (`tcb_ep_dequeue` puts
  the sender into `K`) as IK; the blocking arm `nq_receiveIpcBlocked`.
* `nq_doReplyTransfer J`: from `NQ K` and "no thread of `J` is
  BlockedOnReply" (`NoRpl J`, ft3) to `NQ J` (`J ⊆ K`): the receiver read
  BlockedOnReply joins `K` and is no thread of `J`; its timeout tail
  `nq_replyTail` drops only the receiver.
* `nq_invokeTcb`: one lemma per constructor; ThreadControlSched's
  `set_priority` drops only its target (`nq_invokeTcb_sched`).
-/
import Fl4Proofs.P3.SpecInvNtfnQG2b
import Fl4Proofs.P3.SpecInvNtfnQG2c
import Fl4Proofs.P3.SpecInvNtfnQG2d
