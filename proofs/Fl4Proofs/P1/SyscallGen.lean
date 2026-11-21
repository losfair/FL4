/-
# The general path of `handle_syscall` (FL4 #56)

PR #56 (main 6d1355e) split `handle_syscall` into `syscall s a number fast`:
`handle_syscall` runs it with `fast = true` (the fast paths
`fastpath.fault` / `fastpath.reply_recv` may answer the entry),
`handle_syscall_general` with `fast = false`. `unknown_syscall_fault` and
`handle_unknown_syscall` gained the same `fast` flag and return whether a
fast path ran.

This module keeps the pre-#56 bodies verbatim (`*_old`, copied from the
extraction of main ba3cf690) and proves that the general path is exactly
them:

* `unknown_syscall_fault_false`, `handle_unknown_syscall_false`: with
  `fast = false` the new functions are the old ones with `false` paired on;
* `syscall_false`, `handle_syscall_general_eq`: `handle_syscall_general =
  handle_syscall_old`.

(`handle_trap_syscall` calls `handle_unknown_syscall … false`, so it is the
old one too; no proof here uses it.)

So every P1 / P3 proof about the old entry is a proof about the general
path. The fast paths enter through one named premise only, `FastAgree`
([P], below): at the entry state, what the general path guarantees
`handle_syscall` guarantees too (the theorem fastpath.rs states as
intended).
-/
import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace fl4_core

/-- The pre-#56 body (main ba3cf690), verbatim. -/
def syscall.unknown_syscall_fault_old
  {S : Type _} {A : Type _} (machineStoreInst : machine.Store S)
  (machineArchInst : machine.Arch A) (s : S) (a : A) (number : Std.U64) :
  Result (S × A)
  := do
  let (b, s1, a1) ← syscall.budget_ok machineStoreInst machineArchInst s a
  let (s2, a2) ←
    if b
    then
      do
      let t ← sched.cur_thread machineStoreInst s1
      faults.handle_fault machineStoreInst machineArchInst s1 a1 t
        (error.Fault.UnknownSyscall number)
    else ok (s1, a1)
  syscall.finish machineStoreInst machineArchInst s2 a2

/-- The pre-#56 body (main ba3cf690), verbatim. -/
def syscall.handle_unknown_syscall_old
  {S : Type _} {A : Type _} (machineStoreInst : machine.Store S)
  (machineArchInst : machine.Arch A) (s : S) (a : A) (number : Std.I64) :
  Result (S × A)
  := do
  let t ← sched.cur_thread machineStoreInst s
  if fl4_abi.config.PRINTING
  then
    if number = fl4_abi.syscall.SysDebugPutChar
    then
      let c ← obj.Tcb.reg machineStoreInst t s layout.reg.CAP
      let i ← lift (c &&& 255#u64)
      let a1 ← machineArchInst.putc a i
      ok (s, a1)
    else
      if fl4_abi.config.PRINTING
      then
        if number = fl4_abi.syscall.SysDebugDumpScheduler
        then ok (s, a)
        else
          if fl4_abi.config.DEBUG_BUILD
          then
            let (b, s1, a1) ←
              syscall.debug_syscall machineStoreInst machineArchInst s a t
                number
            if b
            then ok (s1, a1)
            else
              if fl4_abi.config.SET_TLS_BASE_SELF
              then
                if number = fl4_abi.syscall.SysSetTLSBase
                then
                  syscall.set_tls_base_self machineStoreInst machineArchInst s1
                    a1
                else
                  if number = fl4_abi.syscall.SysVMEnter
                  then
                    let i ← machineArchInst.virtualization a1
                    if i != 0#u64
                    then
                      let i1 ← vcpu.bound machineStoreInst s1 t
                      if i1 != 0#u64
                      then
                        let (b1, s2, a2) ←
                          syscall.budget_ok machineStoreInst machineArchInst s1
                            a1
                        let (s3, a3) ←
                          if b1
                          then
                            vcpu.enter machineStoreInst machineArchInst s2 a2 t
                          else ok (s2, a2)
                        syscall.finish machineStoreInst machineArchInst s3 a3
                      else
                        let i2 ← lift (IScalar.hcast .U64 number)
                        syscall.unknown_syscall_fault_old machineStoreInst
                          machineArchInst s1 a1 i2
                    else
                      let i1 ← lift (IScalar.hcast .U64 number)
                      syscall.unknown_syscall_fault_old machineStoreInst
                        machineArchInst s1 a1 i1
                  else
                    let i ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i
              else
                if number = fl4_abi.syscall.SysVMEnter
                then
                  let i ← machineArchInst.virtualization a1
                  if i != 0#u64
                  then
                    let i1 ← vcpu.bound machineStoreInst s1 t
                    if i1 != 0#u64
                    then
                      let (b1, s2, a2) ←
                        syscall.budget_ok machineStoreInst machineArchInst s1
                          a1
                      let (s3, a3) ←
                        if b1
                        then
                          vcpu.enter machineStoreInst machineArchInst s2 a2 t
                        else ok (s2, a2)
                      syscall.finish machineStoreInst machineArchInst s3 a3
                    else
                      let i2 ← lift (IScalar.hcast .U64 number)
                      syscall.unknown_syscall_fault_old machineStoreInst
                        machineArchInst s1 a1 i2
                  else
                    let i1 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i1
                else
                  let i ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i
          else
            if fl4_abi.config.SET_TLS_BASE_SELF
            then
              if number = fl4_abi.syscall.SysSetTLSBase
              then
                syscall.set_tls_base_self machineStoreInst machineArchInst s a
              else
                if number = fl4_abi.syscall.SysVMEnter
                then
                  let i ← machineArchInst.virtualization a
                  if i != 0#u64
                  then
                    let i1 ← vcpu.bound machineStoreInst s t
                    if i1 != 0#u64
                    then
                      let (b, s1, a1) ←
                        syscall.budget_ok machineStoreInst machineArchInst s a
                      let (s2, a2) ←
                        if b
                        then
                          vcpu.enter machineStoreInst machineArchInst s1 a1 t
                        else ok (s1, a1)
                      syscall.finish machineStoreInst machineArchInst s2 a2
                    else
                      let i2 ← lift (IScalar.hcast .U64 number)
                      syscall.unknown_syscall_fault_old machineStoreInst
                        machineArchInst s a i2
                  else
                    let i1 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s a i1
                else
                  let i ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i
            else
              if number = fl4_abi.syscall.SysVMEnter
              then
                let i ← machineArchInst.virtualization a
                if i != 0#u64
                then
                  let i1 ← vcpu.bound machineStoreInst s t
                  if i1 != 0#u64
                  then
                    let (b, s1, a1) ←
                      syscall.budget_ok machineStoreInst machineArchInst s a
                    let (s2, a2) ←
                      if b
                      then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                      else ok (s1, a1)
                    syscall.finish machineStoreInst machineArchInst s2 a2
                  else
                    let i2 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s a i2
                else
                  let i1 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i1
              else
                let i ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i
      else
        if fl4_abi.config.DEBUG_BUILD
        then
          let (b, s1, a1) ←
            syscall.debug_syscall machineStoreInst machineArchInst s a t number
          if b
          then ok (s1, a1)
          else
            if fl4_abi.config.SET_TLS_BASE_SELF
            then
              if number = fl4_abi.syscall.SysSetTLSBase
              then
                syscall.set_tls_base_self machineStoreInst machineArchInst s1
                  a1
              else
                if number = fl4_abi.syscall.SysVMEnter
                then
                  let i ← machineArchInst.virtualization a1
                  if i != 0#u64
                  then
                    let i1 ← vcpu.bound machineStoreInst s1 t
                    if i1 != 0#u64
                    then
                      let (b1, s2, a2) ←
                        syscall.budget_ok machineStoreInst machineArchInst s1
                          a1
                      let (s3, a3) ←
                        if b1
                        then
                          vcpu.enter machineStoreInst machineArchInst s2 a2 t
                        else ok (s2, a2)
                      syscall.finish machineStoreInst machineArchInst s3 a3
                    else
                      let i2 ← lift (IScalar.hcast .U64 number)
                      syscall.unknown_syscall_fault_old machineStoreInst
                        machineArchInst s1 a1 i2
                  else
                    let i1 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i1
                else
                  let i ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i
            else
              if number = fl4_abi.syscall.SysVMEnter
              then
                let i ← machineArchInst.virtualization a1
                if i != 0#u64
                then
                  let i1 ← vcpu.bound machineStoreInst s1 t
                  if i1 != 0#u64
                  then
                    let (b1, s2, a2) ←
                      syscall.budget_ok machineStoreInst machineArchInst s1 a1
                    let (s3, a3) ←
                      if b1
                      then vcpu.enter machineStoreInst machineArchInst s2 a2 t
                      else ok (s2, a2)
                    syscall.finish machineStoreInst machineArchInst s3 a3
                  else
                    let i2 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i2
                else
                  let i1 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i1
              else
                let i ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s1 a1 i
        else
          if fl4_abi.config.SET_TLS_BASE_SELF
          then
            if number = fl4_abi.syscall.SysSetTLSBase
            then syscall.set_tls_base_self machineStoreInst machineArchInst s a
            else
              if number = fl4_abi.syscall.SysVMEnter
              then
                let i ← machineArchInst.virtualization a
                if i != 0#u64
                then
                  let i1 ← vcpu.bound machineStoreInst s t
                  if i1 != 0#u64
                  then
                    let (b, s1, a1) ←
                      syscall.budget_ok machineStoreInst machineArchInst s a
                    let (s2, a2) ←
                      if b
                      then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                      else ok (s1, a1)
                    syscall.finish machineStoreInst machineArchInst s2 a2
                  else
                    let i2 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s a i2
                else
                  let i1 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i1
              else
                let i ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i
          else
            if number = fl4_abi.syscall.SysVMEnter
            then
              let i ← machineArchInst.virtualization a
              if i != 0#u64
              then
                let i1 ← vcpu.bound machineStoreInst s t
                if i1 != 0#u64
                then
                  let (b, s1, a1) ←
                    syscall.budget_ok machineStoreInst machineArchInst s a
                  let (s2, a2) ←
                    if b
                    then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                    else ok (s1, a1)
                  syscall.finish machineStoreInst machineArchInst s2 a2
                else
                  let i2 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i2
              else
                let i1 ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i1
            else
              let i ← lift (IScalar.hcast .U64 number)
              syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s
                a i
  else
    if fl4_abi.config.PRINTING
    then
      if number = fl4_abi.syscall.SysDebugDumpScheduler
      then ok (s, a)
      else
        if fl4_abi.config.DEBUG_BUILD
        then
          let (b, s1, a1) ←
            syscall.debug_syscall machineStoreInst machineArchInst s a t number
          if b
          then ok (s1, a1)
          else
            if fl4_abi.config.SET_TLS_BASE_SELF
            then
              if number = fl4_abi.syscall.SysSetTLSBase
              then
                syscall.set_tls_base_self machineStoreInst machineArchInst s1
                  a1
              else
                if number = fl4_abi.syscall.SysVMEnter
                then
                  let i ← machineArchInst.virtualization a1
                  if i != 0#u64
                  then
                    let i1 ← vcpu.bound machineStoreInst s1 t
                    if i1 != 0#u64
                    then
                      let (b1, s2, a2) ←
                        syscall.budget_ok machineStoreInst machineArchInst s1
                          a1
                      let (s3, a3) ←
                        if b1
                        then
                          vcpu.enter machineStoreInst machineArchInst s2 a2 t
                        else ok (s2, a2)
                      syscall.finish machineStoreInst machineArchInst s3 a3
                    else
                      let i2 ← lift (IScalar.hcast .U64 number)
                      syscall.unknown_syscall_fault_old machineStoreInst
                        machineArchInst s1 a1 i2
                  else
                    let i1 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i1
                else
                  let i ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i
            else
              if number = fl4_abi.syscall.SysVMEnter
              then
                let i ← machineArchInst.virtualization a1
                if i != 0#u64
                then
                  let i1 ← vcpu.bound machineStoreInst s1 t
                  if i1 != 0#u64
                  then
                    let (b1, s2, a2) ←
                      syscall.budget_ok machineStoreInst machineArchInst s1 a1
                    let (s3, a3) ←
                      if b1
                      then vcpu.enter machineStoreInst machineArchInst s2 a2 t
                      else ok (s2, a2)
                    syscall.finish machineStoreInst machineArchInst s3 a3
                  else
                    let i2 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i2
                else
                  let i1 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i1
              else
                let i ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s1 a1 i
        else
          if fl4_abi.config.SET_TLS_BASE_SELF
          then
            if number = fl4_abi.syscall.SysSetTLSBase
            then syscall.set_tls_base_self machineStoreInst machineArchInst s a
            else
              if number = fl4_abi.syscall.SysVMEnter
              then
                let i ← machineArchInst.virtualization a
                if i != 0#u64
                then
                  let i1 ← vcpu.bound machineStoreInst s t
                  if i1 != 0#u64
                  then
                    let (b, s1, a1) ←
                      syscall.budget_ok machineStoreInst machineArchInst s a
                    let (s2, a2) ←
                      if b
                      then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                      else ok (s1, a1)
                    syscall.finish machineStoreInst machineArchInst s2 a2
                  else
                    let i2 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s a i2
                else
                  let i1 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i1
              else
                let i ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i
          else
            if number = fl4_abi.syscall.SysVMEnter
            then
              let i ← machineArchInst.virtualization a
              if i != 0#u64
              then
                let i1 ← vcpu.bound machineStoreInst s t
                if i1 != 0#u64
                then
                  let (b, s1, a1) ←
                    syscall.budget_ok machineStoreInst machineArchInst s a
                  let (s2, a2) ←
                    if b
                    then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                    else ok (s1, a1)
                  syscall.finish machineStoreInst machineArchInst s2 a2
                else
                  let i2 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i2
              else
                let i1 ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i1
            else
              let i ← lift (IScalar.hcast .U64 number)
              syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s
                a i
    else
      if fl4_abi.config.DEBUG_BUILD
      then
        let (b, s1, a1) ←
          syscall.debug_syscall machineStoreInst machineArchInst s a t number
        if b
        then ok (s1, a1)
        else
          if fl4_abi.config.SET_TLS_BASE_SELF
          then
            if number = fl4_abi.syscall.SysSetTLSBase
            then
              syscall.set_tls_base_self machineStoreInst machineArchInst s1 a1
            else
              if number = fl4_abi.syscall.SysVMEnter
              then
                let i ← machineArchInst.virtualization a1
                if i != 0#u64
                then
                  let i1 ← vcpu.bound machineStoreInst s1 t
                  if i1 != 0#u64
                  then
                    let (b1, s2, a2) ←
                      syscall.budget_ok machineStoreInst machineArchInst s1 a1
                    let (s3, a3) ←
                      if b1
                      then vcpu.enter machineStoreInst machineArchInst s2 a2 t
                      else ok (s2, a2)
                    syscall.finish machineStoreInst machineArchInst s3 a3
                  else
                    let i2 ← lift (IScalar.hcast .U64 number)
                    syscall.unknown_syscall_fault_old machineStoreInst
                      machineArchInst s1 a1 i2
                else
                  let i1 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i1
              else
                let i ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s1 a1 i
          else
            if number = fl4_abi.syscall.SysVMEnter
            then
              let i ← machineArchInst.virtualization a1
              if i != 0#u64
              then
                let i1 ← vcpu.bound machineStoreInst s1 t
                if i1 != 0#u64
                then
                  let (b1, s2, a2) ←
                    syscall.budget_ok machineStoreInst machineArchInst s1 a1
                  let (s3, a3) ←
                    if b1
                    then vcpu.enter machineStoreInst machineArchInst s2 a2 t
                    else ok (s2, a2)
                  syscall.finish machineStoreInst machineArchInst s3 a3
                else
                  let i2 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s1 a1 i2
              else
                let i1 ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s1 a1 i1
            else
              let i ← lift (IScalar.hcast .U64 number)
              syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s1
                a1 i
      else
        if fl4_abi.config.SET_TLS_BASE_SELF
        then
          if number = fl4_abi.syscall.SysSetTLSBase
          then syscall.set_tls_base_self machineStoreInst machineArchInst s a
          else
            if number = fl4_abi.syscall.SysVMEnter
            then
              let i ← machineArchInst.virtualization a
              if i != 0#u64
              then
                let i1 ← vcpu.bound machineStoreInst s t
                if i1 != 0#u64
                then
                  let (b, s1, a1) ←
                    syscall.budget_ok machineStoreInst machineArchInst s a
                  let (s2, a2) ←
                    if b
                    then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                    else ok (s1, a1)
                  syscall.finish machineStoreInst machineArchInst s2 a2
                else
                  let i2 ← lift (IScalar.hcast .U64 number)
                  syscall.unknown_syscall_fault_old machineStoreInst
                    machineArchInst s a i2
              else
                let i1 ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i1
            else
              let i ← lift (IScalar.hcast .U64 number)
              syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s
                a i
        else
          if number = fl4_abi.syscall.SysVMEnter
          then
            let i ← machineArchInst.virtualization a
            if i != 0#u64
            then
              let i1 ← vcpu.bound machineStoreInst s t
              if i1 != 0#u64
              then
                let (b, s1, a1) ←
                  syscall.budget_ok machineStoreInst machineArchInst s a
                let (s2, a2) ←
                  if b
                  then vcpu.enter machineStoreInst machineArchInst s1 a1 t
                  else ok (s1, a1)
                syscall.finish machineStoreInst machineArchInst s2 a2
              else
                let i2 ← lift (IScalar.hcast .U64 number)
                syscall.unknown_syscall_fault_old machineStoreInst machineArchInst
                  s a i2
            else
              let i1 ← lift (IScalar.hcast .U64 number)
              syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s
                a i1
          else
            let i ← lift (IScalar.hcast .U64 number)
            syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s a
              i

/-- The pre-#56 body (main ba3cf690), verbatim. -/
def syscall.handle_syscall_old
  {S : Type _} {A : Type _} (machineStoreInst : machine.Store S)
  (machineArchInst : machine.Arch A) (s : S) (a : A) (number : Std.I64) :
  Result (S × A)
  := do
  let t ← sched.cur_thread machineStoreInst s
  let next ← obj.Tcb.reg machineStoreInst t s layout.reg.NEXT_IP
  let i ← lift (core.num.U64.wrapping_sub next 2#u64)
  let s1 ← obj.Tcb.set_reg machineStoreInst t s layout.reg.FAULT_IP i
  let i1 ← obj.Tcb.flags machineStoreInst t s1
  let i2 ← lift (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS)
  if i2 != 0#u64
  then
    let i3 ← lift (IScalar.hcast .U64 number)
    syscall.unknown_syscall_fault_old machineStoreInst machineArchInst s1 a i3
  else
    if number < fl4_abi.syscall.SYSCALL_MIN
    then
      syscall.handle_unknown_syscall_old machineStoreInst machineArchInst s1 a
        number
    else
      if number > fl4_abi.syscall.SYSCALL_MAX
      then
        syscall.handle_unknown_syscall_old machineStoreInst machineArchInst s1 a
          number
      else
        let (b, s2, a1) ←
          syscall.budget_ok machineStoreInst machineArchInst s1 a
        let (s3, a2) ←
          if b
          then
            syscall.dispatch_syscall machineStoreInst machineArchInst s2 a1
              number
          else ok (s2, a1)
        syscall.finish machineStoreInst machineArchInst s3 a2

end fl4_core

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)

/-- **[P] The fast paths keep what the general path guarantees**, for one
postcondition `P` at one entry state (FL4 #56; fastpath.rs: "the intended
theorem is `fast s = (true, s') -> handle_syscall_general s = s'`"). seL4's
counterpart is the fastpath refinement (l4v `Fastpath_C`:
`fastpath_call` / `fastpath_reply_recv` refine the slow path). It is stated
for a postcondition rather than as an equation of results because the fast
paths make the general path's writes in another order ("an order that
gives the same values"): their end state agrees in memory, not necessarily
as a term of an abstract `S`. True wherever the fast paths are correct and
`P` reads the state through memory; where `handle_syscall` cannot take a
fast path it holds outright (`FastAgree.of_eq`). -/
def FastAgree {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A)
    (n : Std.I64) (P : S × A → Prop) : Prop :=
  syscall.handle_syscall_general st ar s a n ⦃ P ⦄ → syscall.handle_syscall st ar s a n ⦃ P ⦄

theorem FastAgree.of_eq {s : S} {a : A} {n : Std.I64} {P : S × A → Prop}
    (h : syscall.handle_syscall st ar s a n = syscall.handle_syscall_general st ar s a n) :
    FastAgree st ar s a n P := fun hg => by rw [h]; exact hg

/-- Reassociate the binds and run the binds of values and the pairs
matched against tuples. -/
local macro "res_norm" : tactic =>
  `(tactic| all_goals try simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte])

/-- Close an equation of two computations that agree after `res_norm`. -/
local macro "res_rfl" : tactic =>
  `(tactic| all_goals first
    | rfl
    | (simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]; done)
    | (simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte]; rfl))

/-- Both sides of the goal start with the computation `e`: reassociate the
binds, then compare the continuations at every value `x` of `e`. -/
local macro "rcase_res " e:term " as " x:ident : tactic =>
  `(tactic| all_goals
    (try simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair]
     all_goals refine congrArg (Std.bind $e) (funext fun $x => ?_)))

theorem unknown_syscall_fault_false (s : S) (a : A) (n : Std.U64) :
    syscall.unknown_syscall_fault st ar s a n false =
      (do let (s', a') ← syscall.unknown_syscall_fault_old st ar s a n; ok (false, s', a')) := by
  unfold syscall.unknown_syscall_fault syscall.unknown_syscall_fault_old
  rcase_res syscall.budget_ok st ar s a as rr1
  all_goals obtain ⟨b, s1, a1⟩ := rr1
  cases b
  · res_norm
    rcase_res syscall.finish st ar s1 a1 as rr2
    all_goals obtain ⟨s2, a2⟩ := rr2
    res_rfl
  · res_norm
    rcase_res sched.cur_thread st s1 as t
    rcase_res faults.handle_fault st ar s1 a1 t (error.Fault.UnknownSyscall n) as rr3
    all_goals obtain ⟨s2, a2⟩ := rr3
    res_norm
    rcase_res syscall.finish st ar s2 a2 as rr4
    all_goals obtain ⟨s3, a3⟩ := rr4
    res_rfl

theorem handle_unknown_syscall_false (s : S) (a : A) (n : Std.I64) :
    syscall.handle_unknown_syscall st ar s a n false =
      (do let (s', a') ← syscall.handle_unknown_syscall_old st ar s a n; ok (false, s', a')) := by
  unfold syscall.handle_unknown_syscall syscall.handle_unknown_syscall_old
  simp only [fl4_abi.config.PRINTING, fl4_abi.config.DEBUG_BUILD, fl4_abi.config.SET_TLS_BASE_SELF,
    ↓reduceIte, lift, bind_ok]
  rcase_res sched.cur_thread st s as t
  by_cases h1 : n = fl4_abi.syscall.SysDebugPutChar
  · simp only [if_pos h1]
    rcase_res obj.Tcb.reg st t s layout.reg.CAP as c
    rcase_res ar.putc a (c &&& 255#u64) as a1
    res_rfl
  simp only [if_neg h1]
  by_cases h2 : n = fl4_abi.syscall.SysDebugDumpScheduler
  · simp only [if_pos h2]; res_rfl
  simp only [if_neg h2]
  rcase_res syscall.debug_syscall st ar s a t n as rr5
  all_goals obtain ⟨b, s1, a1⟩ := rr5
  cases b
  swap
  · res_rfl
  res_norm
  by_cases h3 : n = fl4_abi.syscall.SysSetTLSBase
  · simp only [if_pos h3]
    rcase_res syscall.set_tls_base_self st ar s1 a1 as rr6
    all_goals obtain ⟨s2, a2⟩ := rr6
    res_rfl
  simp only [if_neg h3]
  by_cases h4 : n = fl4_abi.syscall.SysVMEnter
  swap
  · simp only [if_neg h4]; exact unknown_syscall_fault_false st ar _ _ _
  simp only [if_pos h4]
  rcase_res ar.virtualization a1 as i
  by_cases h5 : (i != 0#u64) = true
  swap
  · simp only [if_neg h5]; exact unknown_syscall_fault_false st ar _ _ _
  simp only [if_pos h5]
  rcase_res vcpu.bound st s1 t as i1
  by_cases h6 : (i1 != 0#u64) = true
  swap
  · simp only [if_neg h6]; exact unknown_syscall_fault_false st ar _ _ _
  simp only [if_pos h6]
  rcase_res syscall.budget_ok st ar s1 a1 as rr7
  all_goals obtain ⟨b1, s2, a2⟩ := rr7
  cases b1
  · res_norm
    rcase_res syscall.finish st ar s2 a2 as rr8
    all_goals obtain ⟨s4, a4⟩ := rr8
    res_rfl
  · res_norm
    rcase_res vcpu.enter st ar s2 a2 t as rr9
    all_goals obtain ⟨s3, a3⟩ := rr9
    res_norm
    rcase_res syscall.finish st ar s3 a3 as rr10
    all_goals obtain ⟨s4, a4⟩ := rr10
    res_rfl

/-- `syscall … false` is the pre-#56 entry with `false` paired on. -/
theorem syscall_false (s : S) (a : A) (n : Std.I64) :
    syscall.syscall st ar s a n false =
      (do let (s', a') ← syscall.handle_syscall_old st ar s a n; ok (false, s', a')) := by
  unfold syscall.syscall syscall.handle_syscall_old
  simp only [lift, bind_ok]
  rcase_res sched.cur_thread st s as t
  rcase_res obj.Tcb.reg st t s layout.reg.NEXT_IP as nx
  rcase_res obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) as s1
  rcase_res obj.Tcb.flags st t s1 as f
  by_cases h1 : (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · simp only [if_pos h1, unknown_syscall_fault_false]; res_rfl
  simp only [if_neg h1]
  by_cases h2 : n < fl4_abi.syscall.SYSCALL_MIN
  · simp only [if_pos h2, handle_unknown_syscall_false]; res_rfl
  simp only [if_neg h2]
  by_cases h3 : n > fl4_abi.syscall.SYSCALL_MAX
  · simp only [if_pos h3, handle_unknown_syscall_false]; res_rfl
  simp only [if_neg h3]
  rcase_res syscall.budget_ok st ar s1 a as rr11
  all_goals obtain ⟨b, s2, a1⟩ := rr11
  cases b
  · res_rfl
  · res_norm
    rcase_res syscall.dispatch_syscall st ar s2 a1 n as rr12
    all_goals obtain ⟨s3, a2⟩ := rr12
    res_rfl

/-- **The general path is the pre-#56 entry.** -/
theorem handle_syscall_general_eq (s : S) (a : A) (n : Std.I64) :
    syscall.handle_syscall_general st ar s a n = syscall.handle_syscall_old st ar s a n := by
  unfold syscall.handle_syscall_general
  rw [syscall_false]
  simp only [Std.bind_assoc]
  refine (congrArg (Std.bind (syscall.handle_syscall_old st ar s a n)) (funext fun r => ?_)).trans
    (Std.bind_pure _)
  obtain ⟨s', a'⟩ := r; res_rfl

/-- `FastAgree` turns a triple about the general path into one about
`handle_syscall`. -/
theorem FastAgree.spec {s : S} {a : A} {n : Std.I64} {P : S × A → Prop}
    (hF : FastAgree st ar s a n P) (h : syscall.handle_syscall_old st ar s a n ⦃ P ⦄) :
    syscall.handle_syscall st ar s a n ⦃ P ⦄ :=
  hF (by rw [handle_syscall_general_eq]; exact h)

end
end Fl4Proofs.P1
