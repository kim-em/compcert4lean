import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Cfrontend.Csem
import CompCert4Lean.Cfrontend.Cstrategy
import CompCert4Lean.Cfrontend.SimplExprspec

/-!
# Correctness surface for expression simplification

This module contains the executable definitions and exact proposition
descriptors selected from CompCert's `cfrontend/SimplExprproof.v`.  Proofs are
intentionally left to the later proof-migration phase; no theorem stubs are
introduced here.
-/

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Csem
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev cprogram := CompCert4Lean.Cfrontend.Csyntax.program
private abbrev tprogram := CompCert4Lean.Cfrontend.Clight.program
private abbrev cfunction := CompCert4Lean.Cfrontend.Csyntax.function
private abbrev cexpr := CompCert4Lean.Cfrontend.Csyntax.expr
private abbrev cexprlist := CompCert4Lean.Cfrontend.Csyntax.exprlist
private abbrev cstatement := CompCert4Lean.Cfrontend.Csyntax.statement
private abbrev clabeled_statements :=
  CompCert4Lean.Cfrontend.Csyntax.labeled_statements
private abbrev cfundef := CompCert4Lean.Cfrontend.Csyntax.fundef
private abbrev tfundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev tfunction := CompCert4Lean.Cfrontend.Clight.function
private abbrev cgenv := CompCert4Lean.Cfrontend.Csem.genv
private abbrev tgenv := CompCert4Lean.Cfrontend.Clight.genv
private abbrev cstate := CompCert4Lean.Cfrontend.Csem.state
private abbrev tstate := CompCert4Lean.Cfrontend.Clight.machine_state
private abbrev ccont := CompCert4Lean.Cfrontend.Csem.cont
private abbrev tcont := CompCert4Lean.Cfrontend.Clight.cont
private abbrev cenv := CompCert4Lean.Cfrontend.Csem.env
private abbrev tenv := CompCert4Lean.Cfrontend.Clight.env
private abbrev ttemp_env := CompCert4Lean.Cfrontend.Clight.temp_env
private abbrev ctype := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev trace := CompCert4Lean.Common.Events.trace
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev Included {A : Type} (xs ys : List A) : Prop :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl xs ys

def match_prog
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) (tp : tprogram) : Prop :=
  (list_forall2
      (fun idg tidg =>
        idg.1 = tidg.1 ∧
          match idg.2, tidg.2 with
          | .Gfun f, .Gfun tf =>
              ∃ cu, Ctypes.linkorder_program cu p ∧
                @tr_fundef binary64_certificate binary32_certificate cu f tf
          | .Gvar v, .Gvar tv =>
              v.gvar_info = tv.gvar_info ∧
                v.gvar_init = tv.gvar_init ∧
                v.gvar_readonly = tv.gvar_readonly ∧
                v.gvar_volatile = tv.gvar_volatile
          | _, _ => False)
      (Ctypes.program_of_program p).prog_defs
      (Ctypes.program_of_program tp).prog_defs ∧
    (Ctypes.program_of_program tp).prog_main =
      (Ctypes.program_of_program p).prog_main ∧
    (Ctypes.program_of_program tp).prog_public =
      (Ctypes.program_of_program p).prog_public) ∧
    tp.prog_types = p.prog_types

def Kseqlist : List Clight.statement → Clight.cont → Clight.cont
  | [], k => k
  | s :: rest, k => .Kseq s (Kseqlist rest k)

mutual
  def esize : cexpr → Nat
    | .Eloc _ _ _ _ => 1
    | .Evar _ _ => 1
    | .Ederef r _ => Nat.succ (esize r)
    | .Efield l _ _ => Nat.succ (esize l)
    | .Eval _ _ => 0
    | .Evalof l _ => Nat.succ (esize l)
    | .Eaddrof l _ => Nat.succ (esize l)
    | .Eunop _ r _ => Nat.succ (esize r)
    | .Ebinop _ r1 r2 _ => Nat.succ (esize r1 + esize r2)
    | .Ecast r _ => Nat.succ (esize r)
    | .Eseqand r _ _ => Nat.succ (esize r)
    | .Eseqor r _ _ => Nat.succ (esize r)
    | .Econdition r _ _ _ => Nat.succ (esize r)
    | .Esizeof _ _ => 1
    | .Ealignof _ _ => 1
    | .Eassign l r _ => Nat.succ (esize l + esize r)
    | .Eassignop _ l r _ _ => Nat.succ (esize l + esize r)
    | .Epostincr _ l _ => Nat.succ (esize l)
    | .Ecomma r1 r2 _ => Nat.succ (esize r1 + esize r2)
    | .Ecall r1 rl _ => Nat.succ (esize r1 + esizelist rl)
    | .Ebuiltin _ _ rl _ => Nat.succ (esizelist rl)
    | .Eparen r _ _ => Nat.succ (esize r)

  def esizelist : cexprlist → Nat
    | .Enil => 0
    | .Econs r rest => esize r + esizelist rest
end

def measure : cstate → Nat
  | .ExprState _ r _ _ _ => esize r + 1
  | .State _ .Sskip _ _ _ => 0
  | .State _ (.Sdo r) _ _ _ => esize r + 2
  | .State _ (.Sifthenelse r _ _) _ _ _ => esize r + 2
  | _ => 0

mutual
  inductive match_cont
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (prog : cprogram) (tprog : tprogram) :
      composite_env → ccont → tcont → Prop where
    | match_Kstop (ce : composite_env) :
        match_cont prog tprog ce .Kstop .Kstop
    | match_Kseq (ce : composite_env) (s : cstatement) (k : ccont)
        (ts : Clight.statement) (tk : tcont)
        (hstmt : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kseq s k) (.Kseq ts tk)
    | match_Kwhile2 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kwhile2 r s k)
          (.Kloop1 (.Ssequence s' ts) .Sskip tk)
    | match_Kdowhile1 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kdowhile1 r s k) (.Kloop1 ts s' tk)
    | match_Kfor3 (ce : composite_env) (r : cexpr) (s3 s : cstatement)
        (k : ccont) (ts3 s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs3 : tr_stmt ce s3 ts3)
        (hs : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kfor3 r s3 s k)
          (.Kloop1 (.Ssequence s' ts) ts3 tk)
    | match_Kfor4 (ce : composite_env) (r : cexpr) (s3 s : cstatement)
        (k : ccont) (ts3 s' ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs3 : tr_stmt ce s3 ts3)
        (hs : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kfor4 r s3 s k)
          (.Kloop2 (.Ssequence s' ts) ts3 tk)
    | match_Kswitch2 (ce : composite_env) (k : ccont) (tk : tcont)
        (hk : match_cont prog tprog ce k tk) :
        match_cont prog tprog ce (.Kswitch2 k) (.Kswitch tk)
    | match_Kcall (f : cfunction) (e : tenv) (C : cexpr → cexpr)
        (ty : ctype) (k : ccont) (optid : Option ident) (tf : tfunction)
        (le : ttemp_env) (sl : List Clight.statement) (tk : tcont)
        (a : Clight.expr) (dest : destination) (tmps : List ident)
        (cu : cprogram) (ce : composite_env)
        (hlink : Ctypes.linkorder_program cu prog)
        (htrf : tr_function cu.prog_comp_env f tf)
        (hctx : leftcontext .RV .RV C)
        (htr : ∀ v m, tr_top cu.prog_comp_env (Clight.globalenv tprog) e
          (Clight.set_opttemp optid v le) m dest
          (C (.Eval v ty)) sl a tmps)
        (hmc : match_cont_exp prog tprog cu.prog_comp_env dest a k tk) :
        match_cont prog tprog ce (.Kcall f e C ty k)
          (.Kcall optid tf e le (Kseqlist sl tk))

  inductive match_cont_exp
      [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (prog : cprogram) (tprog : tprogram) :
      composite_env → destination → Clight.expr → ccont → tcont → Prop where
    | match_Kdo (ce : composite_env) (k : ccont) (a : Clight.expr) (tk : tcont)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_effects a (.Kdo k) tk
    | match_Kifthenelse_empty (ce : composite_env) (a : Clight.expr)
        (k : ccont) (tk : tcont) (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a
          (.Kifthenelse .Sskip .Sskip k) (.Kseq .Sskip tk)
    | match_Kifthenelse_1 (ce : composite_env) (a : Clight.expr)
        (s1 s2 : cstatement) (k : ccont) (ts1 ts2 : Clight.statement)
        (tk : tcont) (h1 : tr_stmt ce s1 ts1) (h2 : tr_stmt ce s2 ts2)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a
          (.Kifthenelse s1 s2 k) (.Kseq (.Sifthenelse a ts1 ts2) tk)
    | match_Kwhile1 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' : Clight.statement) (a : Clight.expr)
        (ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kwhile1 r s k)
          (.Kseq (makeif a .Sskip .Sbreak)
            (.Kseq ts (.Kloop1 (.Ssequence s' ts) .Sskip tk)))
    | match_Kdowhile2 (ce : composite_env) (r : cexpr) (s : cstatement)
        (k : ccont) (s' : Clight.statement) (a : Clight.expr)
        (ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs : tr_stmt ce s ts)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kdowhile2 r s k)
          (.Kseq (makeif a .Sskip .Sbreak) (.Kloop2 ts s' tk))
    | match_Kfor2 (ce : composite_env) (r : cexpr) (s3 s : cstatement)
        (k : ccont) (s' : Clight.statement) (a : Clight.expr)
        (ts3 ts : Clight.statement) (tk : tcont)
        (hr : tr_if ce r .Sskip .Sbreak s') (hs3 : tr_stmt ce s3 ts3)
        (hs : tr_stmt ce s ts) (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kfor2 r s3 s k)
          (.Kseq (makeif a .Sskip .Sbreak)
            (.Kseq ts (.Kloop1 (.Ssequence s' ts) ts3 tk)))
    | match_Kswitch1 (ce : composite_env) (ls : clabeled_statements)
        (k : ccont) (a : Clight.expr) (tls : Clight.labeled_statements)
        (tk : tcont) (hls : tr_lblstmts ce ls tls)
        (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kswitch1 ls k)
          (.Kseq (.Sswitch a tls) tk)
    | match_Kreturn (ce : composite_env) (k : ccont) (a : Clight.expr)
        (tk : tcont) (hk : match_cont prog tprog ce k tk) :
        match_cont_exp prog tprog ce .For_val a (.Kreturn k)
          (.Kseq (.Sreturn (some a)) tk)
end

inductive match_states
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (prog : cprogram) (tprog : tprogram) :
    cstate → tstate → Prop where
  | match_exprstates (f : cfunction) (r : cexpr) (k : ccont) (e : cenv)
      (m : mem) (tf : tfunction) (sl : List Clight.statement) (tk : tcont)
      (le : ttemp_env) (dest : destination) (a : Clight.expr)
      (tmps : List ident) (cu : cprogram)
      (hlink : Ctypes.linkorder_program cu prog)
      (htrf : tr_function cu.prog_comp_env f tf)
      (htr : tr_top cu.prog_comp_env (Clight.globalenv tprog) e le m dest r sl a tmps)
      (hmc : match_cont_exp prog tprog cu.prog_comp_env dest a k tk) :
      match_states prog tprog (.ExprState f r k e m)
        (.State tf .Sskip (Kseqlist sl tk) e le m)
  | match_regularstates (f : cfunction) (s : cstatement) (k : ccont)
      (e : cenv) (m : mem) (tf : tfunction) (ts : Clight.statement)
      (tk : tcont) (le : ttemp_env) (cu : cprogram)
      (hlink : Ctypes.linkorder_program cu prog)
      (htrf : tr_function cu.prog_comp_env f tf)
      (htr : tr_stmt cu.prog_comp_env s ts)
      (hmc : match_cont prog tprog cu.prog_comp_env k tk) :
      match_states prog tprog (.State f s k e m)
        (.State tf ts tk e le m)
  | match_callstates (fd : cfundef) (args : List val) (k : ccont) (m : mem)
      (tfd : tfundef) (tk : tcont) (cu : cprogram)
      (hlink : Ctypes.linkorder_program cu prog)
      (htr : tr_fundef cu fd tfd)
      (hmc : ∀ ce, match_cont prog tprog ce k tk) :
      match_states prog tprog (.Callstate fd args k m)
        (.Callstate tfd args tk m)
  | match_returnstates (res : val) (k : ccont) (m : mem) (tk : tcont)
      (hmc : ∀ ce, match_cont prog tprog ce k tk) :
      match_states prog tprog (.Returnstate res k m)
        (.Returnstate res tk m)
  | match_stuckstate (S : tstate) :
      match_states prog tprog .Stuckstate S

export match_states (match_exprstates)

/-! Exact descriptors for later proof migration. -/

def transf_program_matchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ctx p tp, SimplExpr.transl_program ctx p = .OK tp → match_prog p tp

def comp_env_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    (Clight.globalenv tp).genv_cenv = (Csem.globalenv p).genv_cenv

def symbols_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp → ∀ s,
    Genv.find_symbol (Clight.globalenv tp).genv_genv s =
      Genv.find_symbol (Csem.globalenv p).genv_genv s

def senv_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    Senv.equiv (Genv.to_senv (Csem.globalenv p).genv_genv)
      (Genv.to_senv (Clight.globalenv tp).genv_genv)

def function_ptr_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp → ∀ b f,
    Genv.find_funct_ptr (Csem.globalenv p).genv_genv b = some f →
      ∃ cu tf,
        Genv.find_funct_ptr (Clight.globalenv tp).genv_genv b = some tf ∧
          tr_fundef cu f tf ∧ Ctypes.linkorder_program cu p

def functions_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp → ∀ v f,
    Genv.find_funct (Csem.globalenv p).genv_genv v = some f →
      ∃ cu tf,
        Genv.find_funct (Clight.globalenv tp).genv_genv v = some tf ∧
          tr_fundef cu f tf ∧ Ctypes.linkorder_program cu p
def type_of_fundef_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cu f tf, tr_fundef cu f tf → Clight.type_of_fundef tf = Csyntax.type_of_fundef f
def function_return_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce f tf, tr_function ce f tf → tf.fn_return = f.fn_return
def eval_Ederef'Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tge : tgenv) e le m a t l ofs,
    Clight.eval_expr tge e le m a (.Vptr l ofs) →
      Clight.eval_lvalue tge e le m (Ederef' a t) l ofs .Full
def typeof_Ederef'Statement : Prop :=
  ∀ a t, Clight.typeof (Ederef' a t) = t
def eval_Eaddrof'Statement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tge : tgenv) e le m a t l ofs,
    Clight.eval_lvalue tge e le m a l ofs .Full →
      Clight.eval_expr tge e le m (Eaddrof' a t) (.Vptr l ofs)
def typeof_Eaddrof'Statement : Prop :=
  ∀ a t, Clight.typeof (Eaddrof' a t) = t
def eval_make_normalizeStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tge : tgenv) e le m a n sz sg sg1 attr (width : Z),
    ZArith.BinInt.Z.lt .Z0 width →
    ZArith.BinInt.Z.le width (bitsize_intsize sz) →
    Clight.typeof a = .Tint sz sg1 attr →
    Clight.eval_expr tge e le m a (.Vint n) →
    Clight.eval_expr tge e le m
      (make_normalize sz sg width a)
      (.Vint (bitfield_normalize sz sg width n))

def eval_simpl_expr_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ tp e le m a v,
    Clight.eval_expr (Clight.globalenv tp) e le m a v →
      match SimplExpr.eval_simpl_expr a with
      | some v' => v' = v
      | none => True

def tr_simple_nilStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cunit : cprogram,
  (∀ le dst r sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
      (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []) ∧
  (∀ le rl sl al tmps, tr_exprlist cunit.prog_comp_env le rl sl al tmps →
      Cstrategy.simplelist rl = true → sl = [])

def tr_simple_expr_nilStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cunit : cprogram) le dst r sl a tmps,
    tr_expr cunit.prog_comp_env le dst r sl a tmps →
    (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []

def deref_loc_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ ty m b ofs bf t v,
    Csem.deref_loc (Csem.globalenv p) ty m b ofs bf t v →
      match chunk_for_volatile_type ty bf with
      | none => t = E0 ∧ Clight.deref_loc ty m b ofs bf v
      | some chunk => bf = .Full ∧
          volatile_load (Genv.to_senv (Clight.globalenv tp).genv_genv)
            chunk m b ofs t v

def assign_loc_translatedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ ty m b ofs bf v t m' v',
    Csem.assign_loc (Csem.globalenv p) ty m b ofs bf v t m' v' →
      match chunk_for_volatile_type ty bf with
      | none => t = E0 ∧
          Clight.assign_loc (Clight.globalenv tp).genv_cenv ty m b ofs bf v m'
      | some chunk => bf = .Full ∧
          volatile_store (Genv.to_senv (Clight.globalenv tp).genv_genv)
            chunk m b ofs v t m'

def is_bitfield_access_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ cunit : cprogram, Ctypes.linkorder_program cunit p →
    ∀ e le m a b ofs bf bf',
    Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf →
    tr_is_bitfield_access cunit.prog_comp_env a bf' → bf' = bf

def make_assign_value_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p ty m b ofs bf v t m' v',
    Csem.assign_loc (Csem.globalenv p) ty m b ofs bf v t m' v' →
    ∀ (tge : tgenv) e le m'' r, Clight.typeof r = ty →
      Clight.eval_expr tge e le m'' r v →
      Clight.eval_expr tge e le m''
        (make_assign_value bf r) v'
def typeof_make_assign_valueStatement : Prop :=
  ∀ bf r, Clight.typeof (make_assign_value bf r) = Clight.typeof r
def tr_simpleStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) e m,
    (∀ r v, Cstrategy.eval_simple_rvalue (Csem.globalenv p) e m r v →
      ∀ le dst sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
        match dst with
        | .For_val => sl = [] ∧ Csyntax.typeof r = Clight.typeof a ∧
            Clight.eval_expr (Clight.globalenv tp) e le m a v
        | .For_effects => sl = []
        | .For_set sd => ∃ b, sl = do_set sd b ∧
            Csyntax.typeof r = Clight.typeof b ∧
            Clight.eval_expr (Clight.globalenv tp) e le m b v) ∧
    (∀ l b ofs bf,
      Cstrategy.eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf →
      ∀ le sl a tmps, tr_expr cunit.prog_comp_env le .For_val l sl a tmps →
        sl = [] ∧ Csyntax.typeof l = Clight.typeof a ∧
          Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf)

def tr_simple_rvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) e m r v,
    Cstrategy.eval_simple_rvalue (Csem.globalenv p) e m r v →
    ∀ le dst sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
      match dst with
      | .For_val => sl = [] ∧ Csyntax.typeof r = Clight.typeof a ∧
          Clight.eval_expr (Clight.globalenv tp) e le m a v
      | .For_effects => sl = []
      | .For_set sd => ∃ b, sl = do_set sd b ∧
          Csyntax.typeof r = Clight.typeof b ∧
          Clight.eval_expr (Clight.globalenv tp) e le m b v

def tr_simple_lvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) e m l b ofs bf,
    Cstrategy.eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf →
    ∀ le sl a tmps, tr_expr cunit.prog_comp_env le .For_val l sl a tmps →
      sl = [] ∧ Csyntax.typeof l = Clight.typeof a ∧
        Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf

def tr_simple_exprlistStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ p tp, match_prog p tp →
    ∀ (cunit : cprogram) le rl sl al tmps,
    tr_exprlist cunit.prog_comp_env le rl sl al tmps →
    ∀ e m tyl vl,
      Cstrategy.eval_simple_list (Csem.globalenv p) e m rl tyl vl →
      sl = [] ∧ Clight.eval_exprlist (Clight.globalenv tp) e le m al tyl vl

def typeof_contextStatement : Prop :=
  ∀ k1 k2 C, leftcontext k1 k2 C →
    ∀ e1 e2, Csyntax.typeof e1 = Csyntax.typeof e2 →
      Csyntax.typeof (C e1) = Csyntax.typeof (C e2)

def tr_expr_leftcontext_recStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ cunit : cprogram,
  (∀ kfrom kto C, leftcontext kfrom kto C →
    ∀ le e dst sl a tmps, tr_expr cunit.prog_comp_env le dst (C e) sl a tmps →
      ∃ dst' sl1 sl2 a' tmp',
        tr_expr cunit.prog_comp_env le dst' e sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' e' sl3,
          tr_expr cunit.prog_comp_env le' dst' e' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof e' = Csyntax.typeof e →
          tr_expr cunit.prog_comp_env le' dst (C e') (sl3 ++ sl2) a tmps)) ∧
  (∀ kfrom C, leftcontextlist kfrom C →
    ∀ le e sl a tmps, tr_exprlist cunit.prog_comp_env le (C e) sl a tmps →
      ∃ dst' sl1 sl2 a' tmp',
        tr_expr cunit.prog_comp_env le dst' e sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' e' sl3,
          tr_expr cunit.prog_comp_env le' dst' e' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof e' = Csyntax.typeof e →
          tr_exprlist cunit.prog_comp_env le' (C e') (sl3 ++ sl2) a tmps))

def tr_expr_leftcontextStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cunit : cprogram) C le r dst sl a tmps, leftcontext .RV .RV C →
    tr_expr cunit.prog_comp_env le dst (C r) sl a tmps →
      ∃ dst' sl1 sl2 a' tmp',
        tr_expr cunit.prog_comp_env le dst' r sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' r' sl3,
          tr_expr cunit.prog_comp_env le' dst' r' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof r' = Csyntax.typeof r →
          tr_expr cunit.prog_comp_env le' dst (C r') (sl3 ++ sl2) a tmps)

def tr_top_leftcontextStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tprog : tprogram) (cunit : cprogram) e le m dst rtop sl a tmps,
    tr_top cunit.prog_comp_env (Clight.globalenv tprog) e le m dst rtop sl a tmps →
    ∀ r C, rtop = C r → leftcontext .RV .RV C →
      ∃ dst' sl1 sl2 a' tmp',
        tr_top cunit.prog_comp_env (Clight.globalenv tprog)
          e le m dst' r sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧
        Included tmp' tmps ∧
        (∀ le' m' r' sl3,
          tr_expr cunit.prog_comp_env le' dst' r' sl3 a' tmp' →
          (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
          Csyntax.typeof r' = Csyntax.typeof r →
          tr_top cunit.prog_comp_env (Clight.globalenv tprog)
            e le' m' dst (C r') (sl3 ++ sl2) a tmps)

def sem_cast_deterministicStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty ty' m1 v1 m2 v2,
    sem_cast v ty ty' m1 = some v1 → sem_cast v ty ty' m2 = some v2 → v1 = v2

def static_bool_val_soundStatement : Prop :=
  ∀ v t m b, bool_val v t Mem.empty = some b → bool_val v t m = some b

def step_makeifStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) tp f a s1 s2 k e le m v1 b,
    Clight.eval_expr (Clight.globalenv tp) e le m a v1 →
    bool_val v1 (Clight.typeof a) m = some b →
    star (Clight.step1 xi) (Clight.globalenv tp)
      (Clight.State f (makeif a s1 s2) k e le m) E0
      (Clight.State f (if b then s1 else s2) k e le m)

def step_make_setStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) p tp, match_prog p tp →
    ∀ id a ty m b ofs bf t v e le f k,
    Csem.deref_loc (Csem.globalenv p) ty m b ofs bf t v →
    Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf →
    Clight.typeof a = ty →
    Clight.step1 xi
      (Clight.globalenv tp) (Clight.State f (make_set bf id a) k e le m)
      t (Clight.State f .Sskip k e (PTree.set id v le) m)

def step_make_assignStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) p tp, match_prog p tp →
    ∀ a1 a2 ty m b ofs bf t v m' v' v2 e le f k,
    Csem.assign_loc (Csem.globalenv p) ty m b ofs bf v t m' v' →
    Clight.eval_lvalue (Clight.globalenv tp) e le m a1 b ofs bf →
    Clight.eval_expr (Clight.globalenv tp) e le m a2 v2 →
    sem_cast v2 (Clight.typeof a2) ty m = some v →
    Clight.typeof a1 = ty →
    Clight.step1 xi
      (Clight.globalenv tp) (Clight.State f (make_assign bf a1 a2) k e le m)
      t (Clight.State f .Sskip k e le m')
def Kseqlist_appStatement : Prop :=
  ∀ sl1 sl2 k, Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k)

def push_seqStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tp : tprogram) f sl k e le m,
    star (Clight.step1 xi) (Clight.globalenv tp)
      (.State f (SimplExpr.makeseq sl) k e le m) E0
      (.State f .Sskip (Kseqlist sl k) e le m)

def step_tr_rvalofStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ (cu : cprogram), Ctypes.linkorder_program cu p →
    ∀ ty m b ofs bf t v e le a sl a' tmp f k,
      Csem.deref_loc (Csem.globalenv p) ty m b ofs bf t v →
      Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf →
      tr_rvalof cu.prog_comp_env ty a sl a' tmp →
      Clight.typeof a = ty →
      ∃ le',
        star (Clight.step1 xi) (Clight.globalenv tp)
          (.State f .Sskip (Kseqlist sl k) e le m) t
          (.State f .Sskip k e le' m) ∧
        Clight.eval_expr (Clight.globalenv tp) e le' m a' v ∧
        Clight.typeof a' = Clight.typeof a ∧
        ∀ x, x ∉ tmp → PTree.get x le' = PTree.get x le

def match_cont_call_contStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) ce k tk,
    match_cont p tp ce k tk →
    ∀ ce', match_cont p tp ce' (Csem.call_cont k) (Clight.call_cont tk)

def match_cont_is_call_contStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) ce k tk,
    match_cont p tp ce k tk → Csem.is_call_cont k →
    ∀ ce', match_cont p tp ce' k tk

def tr_select_switchStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce n ls tls, tr_lblstmts ce ls tls →
    tr_lblstmts ce (Csem.select_switch n ls) (Clight.select_switch n tls)

def tr_seq_of_labeled_statementStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce ls tls, tr_lblstmts ce ls tls →
    tr_stmt ce (Csem.seq_of_labeled_statement ls)
      (Clight.seq_of_labeled_statement tls)

def tr_find_labelStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) ce lbl s k ts tk,
    tr_stmt ce s ts → match_cont p tp ce k tk →
    match Csem.find_label lbl s k with
    | none => Clight.find_label lbl ts tk = none
    | some (s', k') =>
        ∃ ts' tk', Clight.find_label lbl ts tk = some (ts', tk') ∧
          tr_stmt ce s' ts' ∧ match_cont p tp ce k' tk'

def leftcontext_sizeStatement : Prop :=
  ∀ kfrom kto C, leftcontext kfrom kto C →
    ∀ e1 e2, esize e1 < esize e2 → esize (C e1) < esize (C e2)

def tr_val_genStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ ce le dst v ty a tmp,
    Clight.typeof a = ty →
    (∀ tge e le' m,
      (∀ id, id ∈ tmp → PTree.get id le' = PTree.get id le) →
      Clight.eval_expr tge e le' m a v) →
    tr_expr ce le dst (.Eval v ty) (SimplExprspec.final dst a) a tmp

def estep_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ S1 t S2, Cstrategy.estep xi (Csem.globalenv p) S1 t S2 →
    ∀ S1', match_states p tp S1 S1' →
      ∃ S2',
        (plus (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∨
          (star (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∧
            measure S2 < measure S1)) ∧
        match_states p tp S2 S2'

def tr_top_val_for_val_invStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tp : tprogram) ce e le m v ty sl a tmps,
    tr_top ce (Clight.globalenv tp) e le m .For_val (.Eval v ty) sl a tmps →
    sl = [] ∧ Clight.typeof a = ty ∧
      Clight.eval_expr (Clight.globalenv tp) e le m a v

def alloc_variables_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ e m params e' m',
      Csem.alloc_variables (Csem.globalenv p) e m params e' m' →
      Clight.alloc_variables (Clight.globalenv tp) e m params e' m'

def bind_parameters_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ e m params args m',
      Csem.bind_parameters (Csem.globalenv p) e m params args m' →
      Clight.bind_parameters (Clight.globalenv tp) e m params args m'

def blocks_of_env_preservedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ e, Clight.blocks_of_env (Clight.globalenv tp) e =
      Csem.blocks_of_env (Csem.globalenv p) e

def sstep_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ S1 t S2, Csem.sstep xi (Csem.globalenv p) S1 t S2 →
    ∀ S1', match_states p tp S1 S1' →
      ∃ S2',
        (plus (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∨
          (star (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∧
            measure S2 < measure S1)) ∧
        match_states p tp S2 S2'

def simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    ∀ S1 t S2, Cstrategy.step xi (Csem.globalenv p) S1 t S2 →
    ∀ S1', match_states p tp S1 S1' →
      ∃ S2',
        (plus (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∨
          (star (Clight.step1 xi) (Clight.globalenv tp) S1' t S2' ∧
            measure S2 < measure S1)) ∧
        match_states p tp S2 S2'

def transl_initial_statesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram), match_prog p tp →
    ∀ S, Csem.initial_state p S →
      ∃ S', Clight.initial_state tp S' ∧ match_states p tp S S'

def transl_final_statesStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (p : cprogram) (tp : tprogram) S S' r,
    match_states p tp S S' → Csem.final_state S r → Clight.final_state S' r

def transl_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (p : cprogram) (tp : tprogram),
    match_prog p tp →
    forward_simulation (Cstrategy.semantics xi p) (Clight.semantics1 xi tp)

def TransfSimplExprLinkStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (csyntaxLinkerCertificate : Ctypes.Linker_program_obligations)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations) : Prop :=
  @CompCert4Lean.Common.Linking.TransfLink cprogram tprogram
    (Ctypes.Linker_program cfunction csyntaxLinkerCertificate)
    (Ctypes.Linker_program tfunction clightLinkerCertificate)
    (fun p tp => match_prog p tp)

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem typeof_make_assign_value : typeof_make_assign_valueStatement := by
  intro bf r
  cases bf with
  | Full => rfl
  | Bits size signed pos width =>
      unfold SimplExpr.make_assign_value SimplExpr.make_normalize
      by_cases h : size = .IBool ∨ signed = .Unsigned
      · simp [h, Clight.typeof]
      · simp [h, Clight.typeof]

theorem typeof_context : typeof_contextStatement := by
  intro k1 k2 C h
  cases h <;> intro e1 e2 heq <;> simp_all [Csyntax.typeof]

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem comp_env_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      comp_env_preservedStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp hmatch
  have htypes : tp.prog_types = p.prog_types := hmatch.2
  change tp.prog_comp_env = p.prog_comp_env
  have hp : Ctypes.build_composite_env p.prog_types = .OK p.prog_comp_env :=
    p.prog_comp_env_eq
  have htp : Ctypes.build_composite_env tp.prog_types = .OK tp.prog_comp_env :=
    tp.prog_comp_env_eq
  rw [htypes] at htp
  apply CompCert4Lean.Common.Errors.res.OK.inj
  exact htp.symm.trans hp

private theorem simplexpr_symbol_add_global
    {A B V W : Type} (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (hm : ∀ id', PTree.get id' ge2.genv_symb = PTree.get id' ge1.genv_symb)
    (hn : ge2.genv_next = ge1.genv_next) :
    ∀ id', PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) := by
  intro id'
  have h2 := @PTree.getSet_equation _ id' id ge2.genv_next ge2.genv_symb
  have h1 := @PTree.getSet_equation _ id' id ge1.genv_next ge1.genv_symb
  by_cases h : id' = id
  · rw [h2, h1]
    simp only [dif_pos h]
    exact congrArg some hn
  · rw [h2, h1]
    simp only [dif_neg h]
    exact hm id'

private theorem simplexpr_match_genvs_add_global
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (id : ident)
    (g1 : globdef A V) (g2 : globdef B W)
    (hm : Genv.match_genvs R ge1 ge2) (hg : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  constructor
  · exact congrArg PArith.BinPos.Pos.succ hm.mge_next
  · exact simplexpr_symbol_add_global ge1 ge2 id hm.mge_symb hm.mge_next
  · intro b
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have h1 := @PTree.getSet_equation (globdef A V) b ge1.genv_next g1 ge1.genv_defs
    have h2 := @PTree.getSet_equation (globdef B W) b ge2.genv_next g2 ge2.genv_defs
    by_cases h : b = ge1.genv_next
    · have h' : b = ge2.genv_next := h.trans hm.mge_next.symm
      rw [h1, h2]
      simp only [dif_pos h, dif_pos h']
      exact option_rel.some g1 g2 hg
    · have h' : b ≠ ge2.genv_next := by
        intro hb
        apply h
        exact hb.trans hm.mge_next
      rw [h1, h2]
      simp only [dif_neg h, dif_neg h']
      exact hm.mge_defs b

private theorem simplexpr_match_genvs_add_globals
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (xs : List (ident × globdef A V)) (ys : List (ident × globdef B W))
    (hxy : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) (hm : Genv.match_genvs R ge1 ge2) :
    Genv.match_genvs R (Genv.add_globals ge1 xs) (Genv.add_globals ge2 ys) := by
  induction hxy generalizing ge1 ge2 with
  | nil => simpa [Genv.add_globals] using hm
  | @cons a xs b ys hab htail ih =>
      rcases a with ⟨aid, ag⟩
      rcases b with ⟨bid, bg⟩
      change aid = bid ∧ R ag bg at hab
      rcases hab with ⟨rfl, hab⟩
      simp only [Genv.add_globals, List.foldl_cons]
      apply ih
      exact simplexpr_match_genvs_add_global R ge1 ge2 aid ag bg hm hab

private theorem simplexpr_globalenv_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) (tp : tprogram) (hmatch : match_prog p tp) :
    Genv.match_genvs
      (fun gd1 gd2 => match gd1, gd2 with
        | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧
            @tr_fundef binary64_certificate binary32_certificate cu f tf
        | .Gvar v, .Gvar tv =>
            v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
              v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
        | _, _ => False)
      (Genv.globalenv (Ctypes.program_of_program p))
      (Genv.globalenv (Ctypes.program_of_program tp)) := by
  let R : globdef cfundef type → globdef tfundef type → Prop :=
    fun gd1 gd2 => match gd1, gd2 with
      | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧
          @tr_fundef binary64_certificate binary32_certificate cu f tf
      | .Gvar v, .Gvar tv =>
          v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
            v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
      | _, _ => False
  have hempty : Genv.match_genvs R
      (Genv.empty_genv cfundef type p.prog_public)
      (Genv.empty_genv tfundef type tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none R
  have hlist : list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2)
      (Ctypes.program_of_program p).prog_defs
      (Ctypes.program_of_program tp).prog_defs := by
    change list_forall2 (fun a b => a.1 = b.1 ∧
      (match a.2, b.2 with
        | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧
            @tr_fundef binary64_certificate binary32_certificate cu f tf
        | .Gvar v, .Gvar tv =>
            v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
              v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
        | _, _ => False))
      (Ctypes.program_of_program p).prog_defs
      (Ctypes.program_of_program tp).prog_defs
    exact hmatch.1.1
  exact simplexpr_match_genvs_add_globals R
    (Ctypes.program_of_program p).prog_defs
    (Ctypes.program_of_program tp).prog_defs hlist _ _ hempty

private theorem simplexpr_add_globals_public
    {A V : Type} (ge : Genv.t A V) (gl : List (ident × globdef A V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons idg gl ih =>
      simp only [Genv.add_globals, List.foldl_cons]
      simpa [Genv.add_globals, Genv.add_global] using ih (Genv.add_global ge idg)

theorem symbols_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      symbols_preservedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch s
  exact (simplexpr_globalenv_match p tp hmatch).mge_symb s

theorem senv_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      senv_preservedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch
  have hg := simplexpr_globalenv_match p tp hmatch
  unfold Senv.equiv
  constructor
  · intro id
    exact hg.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program tp)) id =
      Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program p)) id
    have ht0 := simplexpr_add_globals_public
      (Genv.empty_genv tfundef type tp.prog_public)
      (Ctypes.program_of_program tp).prog_defs
    have hp0 := simplexpr_add_globals_public
      (Genv.empty_genv cfundef type p.prog_public)
      (Ctypes.program_of_program p).prog_defs
    have ht : (Genv.globalenv (Ctypes.program_of_program tp)).genv_public = tp.prog_public := by
      unfold Genv.globalenv
      exact ht0
    have hp : (Genv.globalenv (Ctypes.program_of_program p)).genv_public = p.prog_public := by
      unfold Genv.globalenv
      exact hp0
    have hpub : tp.prog_public = p.prog_public := by
      simpa [Ctypes.program_of_program] using hmatch.1.2.2
    unfold Genv.public_symbol
    cases hs : Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program tp)) id with
    | none =>
        have hs' : Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program p)) id = none := by
          exact (hg.mge_symb id).symm.trans hs
        simp [hs']
    | some b =>
        have hs' : Genv.find_symbol (Genv.globalenv (Ctypes.program_of_program p)) id = some b := by
          exact (hg.mge_symb id).symm.trans hs
        simp [hs', ht, hp, hpub]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program tp)) b =
      Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program p)) b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv (Ctypes.program_of_program p)).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hg.mge_defs b
            rw [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none =>
            have hd := hg.mge_defs b
            rw [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hg.mge_defs b
            rw [h1, h2] at hd
            cases hd with
            | some hrel =>
                cases gd1 <;> cases gd2 <;> simp_all

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Lib.Coqlib

theorem function_ptr_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      function_ptr_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch b f hfind
  have hg := simplexpr_globalenv_match p tp hmatch
  have hsrc : Genv.find_def (Genv.globalenv (Ctypes.program_of_program p)) b =
      some (.Gfun f) :=
    (Genv.find_funct_ptr_iff _ _
      (Genv.globalenv (Ctypes.program_of_program p)) b f).mp hfind
  cases htarget : Genv.find_def (Genv.globalenv (Ctypes.program_of_program tp)) b with
  | none =>
      have hd := hg.mge_defs b
      change option_rel _
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program p)) b)
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program tp)) b) at hd
      rw [hsrc, htarget] at hd
      cases hd
  | some gd' =>
      have hd := hg.mge_defs b
      change option_rel _
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program p)) b)
        (Genv.find_def (Genv.globalenv (Ctypes.program_of_program tp)) b) at hd
      rw [hsrc, htarget] at hd
      cases gd' with
      | Gfun tf =>
          cases hd with
          | some _ _ hrel =>
              rcases hrel with ⟨cu, hcu, htr⟩
              refine ⟨cu, tf, ?_, htr, hcu⟩
              change Genv.find_funct_ptr
                (Genv.globalenv (Ctypes.program_of_program tp)) b = some tf
              simp [Genv.find_funct_ptr, htarget]
      | Gvar _ =>
          cases hd with
          | some _ _ hrel => cases hrel

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Globalenvs

theorem functions_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      functions_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch v f hfind
  cases v with
  | Vptr b ofs =>
      simp only [Genv.find_funct] at hfind ⊢
      split at hfind <;> rename_i heq
      · have hptr : Genv.find_funct_ptr (Csem.globalenv p).genv_genv b = some f := by
          simpa [heq] using hfind
        obtain ⟨cu, tf, hptrt, htrans, hlink⟩ :=
          function_ptr_translated p tp hmatch b f hptr
        exact ⟨cu, tf, by simpa [heq, hptrt], htrans, hlink⟩
      · cases hfind
  | Vundef => simp [Genv.find_funct] at hfind
  | Vint n => simp [Genv.find_funct] at hfind
  | Vfloat n => simp [Genv.find_funct] at hfind
  | Vlong n => simp [Genv.find_funct] at hfind
  | Vsingle n => simp [Genv.find_funct] at hfind

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem function_return_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      function_return_preservedStatement := by
  intro binary64_certificate binary32_certificate ce f tf h
  cases h with
  | tr_function_intro _ hreturn _ _ _ => exact hreturn

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem eval_Ederef' :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_Ederef'Statement := by
  intro binary64_certificate binary32_certificate ge e le m a t l ofs h
  unfold Ederef'
  cases a with
  | Eaddrof a' ty' =>
      change Clight.eval_lvalue ge e le m
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Ederef (.Eaddrof a' ty') t) l ofs .Full
      by_cases hc : CompCert4Lean.Lib.Coqlib.proj_sumbool
          (Ctypes.type_eq t (Clight.typeof a')) = true
      · simp [hc]
        cases h with
        | eval_Eaddrof _ _ _ _ hlvalue => exact hlvalue
        | eval_Elvalue _ _ _ _ _ hlvalue hderef => cases hlvalue
      · simp [hc]
        exact Clight.eval_lvalue.eval_Ederef _ _ _ _ h
  | _ => exact Clight.eval_lvalue.eval_Ederef _ _ _ _ h

theorem eval_Eaddrof' :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_Eaddrof'Statement := by
  intro binary64_certificate binary32_certificate ge e le m a t l ofs h
  unfold Eaddrof'
  cases a with
  | Ederef a' ty' =>
      change Clight.eval_expr ge e le m
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Eaddrof (.Ederef a' ty') t) (.Vptr l ofs)
      by_cases hc : CompCert4Lean.Lib.Coqlib.proj_sumbool
          (Ctypes.type_eq t (Clight.typeof a')) = true
      · simp [hc]
        cases h with
        | eval_Ederef _ _ _ _ ha => exact ha
      · simp [hc]
        exact Clight.eval_expr.eval_Eaddrof _ _ _ _ h
  | _ => exact Clight.eval_expr.eval_Eaddrof _ _ _ _ h

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem typeof_Ederef' : typeof_Ederef'Statement := by
  intro a t
  unfold Ederef'
  cases a with
  | Eaddrof a' ty' =>
      change Clight.typeof
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Ederef (.Eaddrof a' ty') t) = t
      cases hte : Ctypes.type_eq t (Clight.typeof a') with
      | left heq =>
          simp [hte, CompCert4Lean.Lib.Coqlib.proj_sumbool, heq]
      | right hneq =>
          simp [CompCert4Lean.Lib.Coqlib.proj_sumbool]
          rfl
  | _ => rfl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem typeof_Eaddrof' : typeof_Eaddrof'Statement := by
  intro a t
  unfold Eaddrof'
  cases a with
  | Ederef a' ty' =>
      change Clight.typeof
        (if CompCert4Lean.Lib.Coqlib.proj_sumbool
            (Ctypes.type_eq t (Clight.typeof a')) = true then a'
          else .Eaddrof (.Ederef a' ty') t) = t
      cases hte : Ctypes.type_eq t (Clight.typeof a') with
      | left heq =>
          simp [hte, CompCert4Lean.Lib.Coqlib.proj_sumbool, heq]
      | right hneq =>
          simp [CompCert4Lean.Lib.Coqlib.proj_sumbool]
          rfl
  | _ => rfl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem tr_simple_nil :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_nilStatement := by
  intro binary64_certificate binary32_certificate cunit
  constructor
  · intro le dst r sl a tmps h
    let P1 := fun (dst : destination) (r : cexpr) (sl : List Clight.statement)
        (a : Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_expr cunit.prog_comp_env le dst r sl a tmps) =>
        (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []
    let P2 := fun (rl : cexprlist) (sl : List Clight.statement)
        (al : List Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_exprlist cunit.prog_comp_env le rl sl al tmps) =>
        Cstrategy.simplelist rl = true → sl = []
    refine SimplExprspec.tr_expr.rec (motive_1 := P1) (motive_2 := P2)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      h
    all_goals
      intros <;> dsimp [P1, P2] at * <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      rintro (rfl | rfl) <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      try (intro hs hv; cases ‹SimplExprspec.tr_rvalof _ _ _ _ _ _› <;> simp_all)
  · intro le rl sl al tmps h
    let P1 := fun (dst : destination) (r : cexpr) (sl : List Clight.statement)
        (a : Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_expr cunit.prog_comp_env le dst r sl a tmps) =>
        (dst = .For_val ∨ dst = .For_effects) → Cstrategy.simple r = true → sl = []
    let P2 := fun (rl : cexprlist) (sl : List Clight.statement)
        (al : List Clight.expr) (tmps : List ident)
        (_ : SimplExprspec.tr_exprlist cunit.prog_comp_env le rl sl al tmps) =>
        Cstrategy.simplelist rl = true → sl = []
    refine SimplExprspec.tr_exprlist.rec (motive_1 := P1) (motive_2 := P2)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    all_goals
      intros <;> dsimp [P1, P2] at * <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      rintro (rfl | rfl) <;>
        simp_all [Cstrategy.simple, Cstrategy.simplelist, SimplExprspec.final]
    all_goals
      try (intro hs hv; cases ‹SimplExprspec.tr_rvalof _ _ _ _ _ _› <;> simp_all)

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem tr_simple_expr_nil :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_expr_nilStatement := by
  intro binary64_certificate binary32_certificate cunit le dst r sl a tmps h hdst hsimple
  exact (tr_simple_nil (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) cunit).1
    le dst r sl a tmps h hdst hsimple

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

private theorem simplexpr_volatile_store_preserved
    (ge1 ge2 : CompCert4Lean.Common.Globalenvs.Senv.t)
    (chunk : CompCert4Lean.Common.AST.memory_chunk)
    (m1 : mem) (b : block) (ofs : ptrofs) (v : val) (t : trace) (m2 : mem)
    (heq : CompCert4Lean.Common.Globalenvs.Senv.equiv ge1 ge2)
    (hstore : CompCert4Lean.Common.Events.volatile_store ge1 chunk m1 b ofs v t m2) :
    CompCert4Lean.Common.Events.volatile_store ge2 chunk m1 b ofs v t m2 := by
  cases hstore with
  | volatile_store_vol id ev v is_volatile find_symbol eventval_matches =>
      apply CompCert4Lean.Common.Events.volatile_store_vol
      · rw [heq.2.2 b]
        exact is_volatile
      · rw [heq.1 _]
        exact find_symbol
      · exact CompCert4Lean.Common.Events.eventval_match_preserved
          ge1 ge2 heq.2.1 heq.1 ev _
            (CompCert4Lean.Common.Values.Val.load_result chunk v) eventval_matches
  | volatile_store_nonvol v m' not_volatile store =>
      apply CompCert4Lean.Common.Events.volatile_store_nonvol
      · rw [heq.2.2 b]
        exact not_volatile
      · exact store

theorem assign_loc_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      assign_loc_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch ty m b ofs bf v t m' v' h
  cases h with
  | value hmode hvol hstore =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact Clight.assign_loc_value _ _ _ hmode hstore
  | volatile hmode hvol hstore =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact simplexpr_volatile_store_preserved _ _ _ _ _ _ _ _ _
        (senv_preserved (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) p tp hmatch)
        hstore
  | copy hmode halignSource halignTarget hseparated hload hstore =>
      have henv : (Clight.globalenv tp).genv_cenv = (Csem.globalenv p).genv_cenv := by
        exact comp_env_preserved (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) p tp hmatch
      simp [chunk_for_volatile_type, Ctypes.type_is_volatile, hmode]
      rw [henv]
      apply Clight.assign_loc_copy _ _ _ _ hmode
      · intro hsize
        exact halignSource
      · intro hsize
        exact halignTarget
      · exact hseparated
      · exact hload
      · exact hstore
  | bitfield hstore =>
      unfold chunk_for_volatile_type
      by_cases hvol : Ctypes.type_is_volatile ty = true
      · simp [hvol]
        cases hmode : Ctypes.access_mode ty <;> simp [hmode]
        all_goals exact Clight.assign_loc_bitfield _ _ _ _ _ _ _ hstore
      · simp [hvol]
        exact Clight.assign_loc_bitfield _ _ _ _ _ _ _ hstore

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem deref_loc_translated :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      deref_loc_translatedStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch ty m b ofs bf t v h
  cases h with
  | value hmode hvol hload =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact Clight.deref_loc_value _ _ hmode hload
  | volatile hmode hvol hload =>
      simp [chunk_for_volatile_type, hvol, hmode]
      exact CompCert4Lean.Common.Events.volatile_load_preserved
        (ge1 := CompCert4Lean.Common.Globalenvs.Genv.to_senv (Csem.globalenv p).genv_genv)
        (ge2 := CompCert4Lean.Common.Globalenvs.Genv.to_senv (Clight.globalenv tp).genv_genv)
        (chunk := _) (m := m) (b := b) (ofs := ofs) (t := t) (v := v)
        (senv_preserved (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) p tp hmatch)
        hload
  | reference hmode =>
      simp [chunk_for_volatile_type, hmode]
      exact Clight.deref_loc_reference hmode
  | copy hmode =>
      simp [chunk_for_volatile_type, hmode]
      exact Clight.deref_loc_copy hmode
  | bitfield hload =>
      cases hvol : Ctypes.type_is_volatile ty with
      | false =>
          simp [chunk_for_volatile_type, hvol]
          exact Clight.deref_loc_bitfield _ _ _ _ _ hload
      | true =>
          cases hmode : Ctypes.access_mode ty with
          | By_value chunk =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload
          | By_reference =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload
          | By_copy =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload
          | By_nothing =>
              simp [chunk_for_volatile_type, hvol, hmode]
              exact Clight.deref_loc_bitfield _ _ _ _ _ hload

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

private theorem simplexpr_add_composite_defs_consistent :
    ∀ (defs : List Ctypes.composite_definition) (env1 env2 : Ctypes.composite_env),
      Ctypes.add_composite_definitions env1 defs = .OK env2 →
      Ctypes.composite_env_consistent env1 →
      Ctypes.composite_env_consistent env2 := by
  intro defs
  induction defs with
  | nil =>
      intro env1 env2 hadd hbase
      simp only [Ctypes.add_composite_definitions] at hadd
      cases hadd
      exact hbase
  | cons d defs ih =>
      intro env1 env2 hadd hbase
      change PTree.tree Ctypes.composite at env1 env2
      cases d with
      | Composite id su ms a =>
          cases hco : Ctypes.composite_of_def env1 id su ms a with
          | Error msg =>
              simp [Ctypes.add_composite_definitions, hco] at hadd
          | OK co =>
              have hrest :
                  Ctypes.add_composite_definitions (PTree.set id co env1) defs =
                    .OK env2 := by
                simpa [Ctypes.add_composite_definitions, hco] using hadd
              have hco_cons : Ctypes.composite_consistent env1 co :=
                Ctypes.composite_of_def_consistent env1 id su ms a co hco
              have hnone : PTree.get
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  env1 = none := by
                unfold Ctypes.composite_of_def at hco
                split at hco
                · rename_i hdup
                  cases hco
                · rename_i hnone
                  exact hnone
              have hincr : ∀ j cj, PTree.get j env1 = some cj →
                  PTree.get j (PTree.set id co env1) = some cj := by
                intro j cj hj
                have hs := PTree.getSet_equation (A := Ctypes.composite)
                  j (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  co env1
                rw [hs]
                split
                · rename_i hEq
                  exfalso
                  cases hEq
                  have hbad : (none : Option Ctypes.composite) = some cj :=
                    hnone.symm.trans hj
                  cases hbad
                · exact hj
              have hset : Ctypes.composite_env_consistent (PTree.set id co env1) := by
                intro j cj hj
                have hspec := PTree.getSet_equation (A := Ctypes.composite)
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from j)
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  co env1
                rw [hspec] at hj
                split at hj
                · rename_i hEq
                  cases hEq
                  cases hj
                  exact Ctypes.composite_consistent_stable env1
                    (PTree.set id co env1) hincr co hco_cons
                · exact Ctypes.composite_consistent_stable env1
                    (PTree.set id co env1) hincr cj (hbase j cj hj)
              exact ih (PTree.set id co env1) env2 hrest hset

private theorem simplexpr_cenv_consistent
    (cunit : cprogram) :
    Ctypes.composite_env_consistent cunit.prog_comp_env := by
  have hempty : Ctypes.composite_env_consistent
      (show Ctypes.composite_env from PTree.empty Ctypes.composite) := by
    intro id co hget
    change PTree.get (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
      (PTree.empty Ctypes.composite) = some co at hget
    simp only [PTree.empty, PTree.get] at hget
    cases hget
  exact simplexpr_add_composite_defs_consistent cunit.prog_types
    (show Ctypes.composite_env from PTree.empty Ctypes.composite)
    cunit.prog_comp_env cunit.prog_comp_env_eq hempty

private theorem simplexpr_cenv_inclusion_for_bitfield
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (p : cprogram) (tp : tprogram) (cunit : cprogram)
    (hmatch : match_prog p tp)
    (hlink : Ctypes.linkorder_program cunit p) :
    ∀ id co, PTree.get id cunit.prog_comp_env = some co →
      PTree.get id (Clight.globalenv tp).genv_cenv = some co := by
  intro id co hget
  have hp := hlink.2 id co hget
  have henv : (Clight.globalenv tp).genv_cenv =
      (Csem.globalenv p).genv_cenv :=
    comp_env_preserved (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) p tp hmatch
  rw [henv]
  exact hp

private theorem simplexpr_bitfield_composite_lookup
    (cunit : cprogram)
    (tp : tprogram)
    (hinc : ∀ id co, PTree.get id cunit.prog_comp_env = some co →
      PTree.get id (Clight.globalenv tp).genv_cenv = some co)
    (id : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (co co' : Ctypes.composite)
    (hget : PTree.get id (Clight.globalenv tp).genv_cenv = some co)
    (hget' : PTree.get id cunit.prog_comp_env = some co') :
    co' = co ∧ complete_members cunit.prog_comp_env co'.co_members = true := by
  have hget'' := hinc id co' hget'
  have heq : co' = co := Option.some.inj (hget''.symm.trans hget)
  have hconsistent : composite_env_consistent cunit.prog_comp_env :=
    simplexpr_cenv_consistent cunit
  have hco := hconsistent id co' hget'
  exact ⟨heq, hco.co_consistent_complete⟩

theorem is_bitfield_access_sound :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      is_bitfield_access_soundStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit hlink
  have hinc := simplexpr_cenv_inclusion_for_bitfield
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp cunit hmatch hlink
  intro e le m a b ofs bf bf' hEval htr
  cases hEval with
  | eval_Evar_local id loc ty hfind =>
      simpa [tr_is_bitfield_access] using htr
  | eval_Evar_global id loc ty hlocal hglobal =>
      simpa [tr_is_bitfield_access] using htr
  | eval_Ederef a ty loc ofs ha =>
      simpa [tr_is_bitfield_access] using htr
  | eval_Efield_struct a id ty loc ofs structId co att delta bf ha htype hcomposite hoffset =>
      simp only [tr_is_bitfield_access] at htr
      rw [htype] at htr
      rcases htr with ⟨co', ofs', hcomposite', hoffset'⟩
      rcases simplexpr_bitfield_composite_lookup cunit tp hinc structId co co'
        hcomposite hcomposite' with ⟨hEq, hcomplete⟩
      subst co'
      have hstable := Ctypes.field_offset_stable
        cunit.prog_comp_env (Clight.globalenv tp).genv_cenv hinc id
        (Ctypes.composite.co_members co)
        hcomplete
      have hpairs : (delta, bf) = (ofs', bf') :=
        CompCert4Lean.Common.Errors.res.OK.inj
          (hoffset.symm.trans (hstable.trans hoffset'))
      exact (congrArg Prod.snd hpairs).symm
  | eval_Efield_union a id ty loc ofs unionId co att delta bf ha htype hcomposite hoffset =>
      simp only [tr_is_bitfield_access] at htr
      rw [htype] at htr
      rcases htr with ⟨co', ofs', hcomposite', hoffset'⟩
      rcases simplexpr_bitfield_composite_lookup cunit tp hinc unionId co co'
        hcomposite hcomposite' with ⟨hEq, hcomplete⟩
      subst co'
      have hstable := Ctypes.union_field_offset_stable
        cunit.prog_comp_env (Clight.globalenv tp).genv_cenv hinc id
        (Ctypes.composite.co_members co)
        hcomplete
      have hpairs : (delta, bf) = (ofs', bf') :=
        CompCert4Lean.Common.Errors.res.OK.inj
          (hoffset.symm.trans (hstable.trans hoffset'))
      exact (congrArg Prod.snd hpairs).symm

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.Cop

theorem tr_simple_rvalue :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_rvalueStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit e m r v hEval
  let P1 := fun (l : cexpr) (b : block) (ofs : ptrofs) (bf : bitfield)
      (_ : Cstrategy.eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf) =>
      ∀ le sl a tmps, tr_expr cunit.prog_comp_env le .For_val l sl a tmps →
        sl = [] ∧ Csyntax.typeof l = Clight.typeof a ∧
          Clight.eval_lvalue (Clight.globalenv tp) e le m a b ofs bf
  let P2 := fun (r : cexpr) (v : val)
      (_ : Cstrategy.eval_simple_rvalue (Csem.globalenv p) e m r v) =>
      ∀ le dst sl a tmps, tr_expr cunit.prog_comp_env le dst r sl a tmps →
      match dst with
      | .For_val => sl = [] ∧ Csyntax.typeof r = Clight.typeof a ∧
          Clight.eval_expr (Clight.globalenv tp) e le m a v
      | .For_effects => sl = []
      | .For_set sd => ∃ b, sl = do_set sd b ∧
          Csyntax.typeof r = Clight.typeof b ∧
          Clight.eval_expr (Clight.globalenv tp) e le m b v
  have hrec : P2 r v hEval := by
    refine Cstrategy.eval_simple_rvalue.rec (motive_1 := P1) (motive_2 := P2)
      (esl_loc := by
        intro b ofs ty bf
        dsimp [P1]
        intro le sl a tmps htr
        cases htr)
      (esl_var_local := by
        intro x ty b hfind
        dsimp [P1]
        intro le sl a tmps htr
        cases htr with
        | tr_var =>
            simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
            exact Clight.eval_lvalue.eval_Evar_local _ _ _ hfind)
      (esl_var_global := by
        intro x ty b hlocal hglobal
        dsimp [P1]
        intro le sl a tmps htr
        cases htr with
        | tr_var =>
            simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
            apply Clight.eval_lvalue.eval_Evar_global _ _ _ hlocal
            have hs := symbols_preserved
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) p tp hmatch
              (show CompCert4Lean.Common.AST.ident from x)
            rw [hs]
            exact hglobal)
      (esl_deref := by
        intro r ty b ofs heval ih
        dsimp [P1]
        intro le sl a tmps htr
        cases htr with
        | tr_deref le dst ty' sl1 a1 tmp h1 =>
          have hi := ih le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · simp only [Csyntax.typeof]
              exact (typeof_Ederef' _ _).symm
            · apply eval_Ederef'
              exact hev)
      (esl_field_struct := by
        intro r f ty b ofs id co att delta bf heval htype hcomp hoffset ih
        dsimp [P1]
        intro le sl a tmps htr
        cases htr
        case tr_field =>
          have hi := ih le .For_val _ _ _ (by assumption)
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof _ = .Tstruct id att :=
                hty.symm.trans htype
              have hcomp' : PTree.get id (Clight.globalenv tp).genv_cenv = some co := by
                rw [henv]
                exact hcomp
              have hoffset' : field_offset (Clight.globalenv tp).genv_cenv
                  f co.co_members = .OK (delta, bf) := by
                rw [henv]
                exact hoffset
              apply Clight.eval_lvalue.eval_Efield_struct
              · exact hev
              · exact htype'
              · exact hcomp'
              · exact hoffset')
      (esl_field_union := by
        intro r f ty b ofs id co att delta bf heval htype hoffset hcomp ih
        dsimp [P1]
        intro le sl a tmps htr
        cases htr
        case tr_field =>
          have hi := ih le .For_val _ _ _ (by assumption)
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof _ = .Tunion id att :=
                hty.symm.trans htype
              have hcomp' : PTree.get id (Clight.globalenv tp).genv_cenv = some co := by
                rw [henv]
                exact hcomp
              have hoffset' : union_field_offset (Clight.globalenv tp).genv_cenv
                  f co.co_members = .OK (delta, bf) := by
                rw [henv]
                exact hoffset
              apply Clight.eval_lvalue.eval_Efield_union
              · exact hev
              · exact htype'
              · exact hcomp'
              · exact hoffset')
      (esr_val := by
        intro v ty
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_val_effect => simp
        | tr_val_value =>
            simp
            constructor
            · exact (by assumption : Clight.typeof _ = _).symm
            · apply_assumption
              intro id hid
              rfl
        | tr_val_set le sd a0 any tmp htype heval =>
            simp
            refine ⟨any, rfl, ?_, ?_⟩
            · exact heval.symm
            · apply_assumption
              intro id hid
              rfl)
      (esr_rvalof := by
        intro b ofs bf l ty v heval hty hvol hderef ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_valof le dst ty' tmp sl1 a1 tmp1 sl2 a2 tmp2 h1 h2 hdisjoint hincl1 hincl2 =>
          cases h2 with
          | tr_rvalof_nonvol =>
            have hi := ih le sl1 a tmp1 h1
            rcases hi with ⟨hsl, htype, hlval⟩
            have hd := deref_loc_translated
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate) p tp hmatch
              ty m b ofs bf CompCert4Lean.Common.Events.E0 v hderef
            simp [chunk_for_volatile_type, hvol] at hd
            cases dst
            · rw [hsl]
              simp only [SimplExprspec.final, List.nil_append]
              have hta : Clight.typeof a = ty := htype.symm.trans hty.symm
              constructor
              · simp
              · constructor
                · simp only [Csyntax.typeof]
                  exact hta.symm
                · apply Clight.eval_expr.eval_Elvalue
                  · exact hlval
                  · simpa [hta] using hd
            · rw [hsl]
              simp only [SimplExprspec.final, List.nil_append]
            · rw [hsl]
              simp only [SimplExprspec.final, List.nil_append]
              refine ⟨a, rfl, ?_, ?_⟩
              · exact hty.trans htype
              · apply Clight.eval_expr.eval_Elvalue
                · exact hlval
                · have hta : Clight.typeof a = ty := htype.symm.trans hty.symm
                  simpa [hta] using hd
          | tr_rvalof_vol =>
            simp_all)
      (esr_addrof := by
        intro b ofs l ty heval ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr
        case tr_addrof =>
          have hi := ih le _ _ _ (by assumption)
          rcases hi with ⟨hsl, htype, hlval⟩
          cases dst
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            constructor
            · simp
            · constructor
              · exact (typeof_Eaddrof' _ _).symm
              · apply eval_Eaddrof'
                exact hlval
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            refine ⟨_, rfl, ?_, ?_⟩
            · exact (typeof_Eaddrof' _ _).symm
            · apply eval_Eaddrof'
              exact hlval)
      (esr_unop := by
        intro op r1 ty v1 v heval hsem ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_unop le dst op' ty' tmp sl1 a1 h1 =>
          have hi := ih le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, htype, hev⟩
          have hsem' : sem_unary_operation op v1 (Clight.typeof a1) m = some v := by
            rw [← htype]
            exact hsem
          cases dst
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            constructor
            · simp
            · constructor
              · rfl
              · apply Clight.eval_expr.unary
                · exact hev
                · exact hsem'
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · apply Clight.eval_expr.unary
              · exact hev
              · exact hsem')
      (esr_binop := by
        intro op r1 r2 ty v1 v2 v heval1 heval2 hsem ih1 ih2
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_binop le dst op' e2 ty' sl1 a1 tmp1 sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 =>
          have hi1 := ih1 le .For_val sl1 a1 tmp1 h1
          have hi2 := ih2 le .For_val sl2 a2 tmp2 h2
          rcases hi1 with ⟨hsl1, htype1, hev1⟩
          rcases hi2 with ⟨hsl2, htype2, hev2⟩
          have henv := comp_env_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
          have hsem' : sem_binary_operation (Clight.globalenv tp).genv_cenv
              op v1 (Clight.typeof a1) v2 (Clight.typeof a2) m = some v := by
            rw [henv, ← htype1, ← htype2]
            exact hsem
          cases dst
          · rw [hsl1, hsl2]
            simp only [SimplExprspec.final, List.nil_append, List.append_nil]
            constructor
            · simp
            · constructor
              · rfl
              · apply Clight.eval_expr.binary
                · exact hev1
                · exact hev2
                · exact hsem'
          · rw [hsl1, hsl2]
            simp only [SimplExprspec.final, List.nil_append, List.append_nil]
          · rw [hsl1, hsl2]
            simp only [SimplExprspec.final, List.nil_append, List.append_nil]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · apply Clight.eval_expr.binary
              · exact hev1
              · exact hev2
              · exact hsem')
      (esr_cast := by
        intro ty r1 v1 v heval hsem ih
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr with
        | tr_cast_effects le ty' sl1 a1 any tmp h1 =>
          simpa using (ih le .For_effects sl a1 tmps h1)
        | tr_cast_val le dst ty' sl1 a1 tmp h1 =>
          have hi := ih le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, htype, hev⟩
          have hsem' : sem_cast v1 (Clight.typeof a1) ty m = some v := by
            rw [← htype]
            exact hsem
          cases dst
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            constructor
            · simp
            · constructor
              · rfl
              · apply Clight.eval_expr.cast
                · exact hev
                · exact hsem'
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
          · rw [hsl]
            simp only [SimplExprspec.final, List.nil_append]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · apply Clight.eval_expr.cast
              · exact hev
              · exact hsem')
      (esr_sizeof := by
        intro ty1 ty
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr
        case tr_sizeof =>
          have henv := comp_env_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
          cases dst
          · simp only [SimplExprspec.final]
            constructor
            · simp
            · constructor
              · rfl
              · simpa only [henv] using
                  (Clight.eval_expr.sizeof_type
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    (ge := Clight.globalenv tp)
                    (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty)
          · simp only [SimplExprspec.final]
          · simp only [SimplExprspec.final]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · simpa only [henv] using
                (Clight.eval_expr.sizeof_type
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (ge := Clight.globalenv tp)
                  (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty))
      (esr_alignof := by
        intro ty1 ty
        dsimp [P2]
        intro le dst sl a tmps htr
        cases htr
        case tr_alignof =>
          have henv := comp_env_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
          cases dst
          · simp only [SimplExprspec.final]
            constructor
            · simp
            · constructor
              · rfl
              · simpa only [henv] using
                  (Clight.eval_expr.alignof_type
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    (ge := Clight.globalenv tp)
                    (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty)
          · simp only [SimplExprspec.final]
          · simp only [SimplExprspec.final]
            refine ⟨_, rfl, ?_, ?_⟩
            · rfl
            · simpa only [henv] using
                (Clight.eval_expr.alignof_type
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (ge := Clight.globalenv tp)
                  (e := (show Clight.env from e)) (le := le) (m := m) ty1 ty))
      hEval
  simpa [P2] using hrec

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

theorem tr_simple_lvalue :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_lvalueStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit e m l b ofs bf hEval
  intro le sl a tmps htr
  cases hEval with
  | esl_loc =>
      cases htr
  | esl_var_local hfind =>
      cases htr with
      | tr_var =>
          simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
          exact Clight.eval_lvalue.eval_Evar_local _ _ _ hfind
  | @esl_var_global x ty b hlocal hglobal =>
      cases htr with
      | tr_var =>
          simp [SimplExprspec.final, Csyntax.typeof, Clight.typeof]
          apply Clight.eval_lvalue.eval_Evar_global _ _ _ hlocal
          have hs := symbols_preserved
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            (show CompCert4Lean.Common.AST.ident from x)
          rw [hs]
          exact hglobal
  | esl_deref heval =>
      cases htr with
      | tr_deref le dst ty' sl1 a1 tmp h1 =>
          have hi := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m _ _ heval) le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, htype, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · simp only [Csyntax.typeof]
              exact (typeof_Ederef' _ _).symm
            · apply eval_Ederef'
              exact hev
  | esl_field_struct heval htype hcomp hoffset =>
      cases htr with
      | tr_field le dst f ty' sl1 a1 tmp h1 =>
          have hi := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m _ _ heval) le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof a1 = .Tstruct _ _ :=
                hty.symm.trans htype
              apply Clight.eval_lvalue.eval_Efield_struct
              · exact hev
              · exact htype'
              · rw [henv]
                exact hcomp
              · rw [henv]
                exact hoffset
  | esl_field_union heval htype hoffset hcomp =>
      cases htr with
      | tr_field le dst f ty' sl1 a1 tmp h1 =>
          have hi := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m _ _ heval) le .For_val sl1 a1 tmps h1
          rcases hi with ⟨hsl, hty, hev⟩
          rw [hsl]
          simp only [SimplExprspec.final, List.nil_append]
          constructor
          · simp
          · constructor
            · rfl
            · have henv := comp_env_preserved
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
              have htype' : Clight.typeof a1 = .Tunion _ _ :=
                hty.symm.trans htype
              apply Clight.eval_lvalue.eval_Efield_union
              · exact hev
              · exact htype'
              · rw [henv]
                exact hcomp
              · rw [henv]
                exact hoffset

end CompCert4Lean.Cfrontend.SimplExprproof
namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

theorem tr_simple_exprlist :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simple_exprlistStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit le rl sl al tmps htr
  intro e m tyl vl hEval
  induction hEval generalizing sl al tmps with
  | esrl_nil =>
      cases htr
      constructor
      · rfl
      · exact Clight.eval_exprlist.nil
  | @esrl_cons r rl ty tyl v vl v' hr hcast hrest ih =>
      cases htr with
      | tr_cons x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =>
          have hi1 := (tr_simple_rvalue
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) p tp hmatch
            cunit e m r v' hr) le .For_val x3 x4 x5 x10
          have hi2 := ih x6 x7 x8 x11
          rcases hi1 with ⟨hs1, htype1, hev1⟩
          rcases hi2 with ⟨hs2, hev2⟩
          constructor
          · simp [hs1, hs2]
          · apply Clight.eval_exprlist.cons
            · exact hev1
            · rw [← htype1]
              exact hcast
            · exact hev2

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.Cop

theorem sem_cast_deterministic
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    sem_cast_deterministicStatement := by
  intro v ty ty' m1 v1 m2 v2 h1 h2
  unfold sem_cast at h1 h2
  cases hclass : classify_cast ty ty' <;>
    cases v <;>
    simp [hclass] at h1 h2
  all_goals
    first
    | exact h1.symm.trans h2
    | exact h1.2.symm.trans h2.2
    | exact h1.2.2.symm.trans h2.2.2
    | rcases h1 with ⟨a, ha, h1⟩
      rcases h2 with ⟨b, hb, h2⟩
      have hab : a = b := Option.some.inj (ha.symm.trans hb)
      subst b
      exact h1.symm.trans h2

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Csyntax
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Memory

theorem eval_simpl_expr_sound :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_simpl_expr_soundStatement := by
  intro binary64_certificate binary32_certificate tp e le m a v hEval
  let P : Clight.expr → val → Prop := fun a v =>
    match eval_simpl_expr a with
    | some v' => v' = v
    | none => True
  let P0 : Clight.expr → block → ptrofs → Ctypes.bitfield → Prop :=
    fun a _ _ _ => eval_simpl_expr a = none
  have hP : P a v := by
    refine Clight.eval_expr.rec
      (motive_1 := fun a v _ => P a v)
      (motive_2 := fun a _ _ _ _ => eval_simpl_expr a = none)
      (const_int := by intro i ty; simp [P, eval_simpl_expr])
      (const_float := by intro f ty; simp [P, eval_simpl_expr])
      (const_single := by intro f ty; simp [P, eval_simpl_expr])
      (const_long := by intro i ty; simp [P, eval_simpl_expr])
      (eval_Etempvar := by intro id ty v hfind; simp [P, eval_simpl_expr])
      (eval_Eaddrof := by intro a ty loc ofs hl ih; simp [P, eval_simpl_expr])
      (unary := by intro op a ty v1 v ha hop ih; simp [P, eval_simpl_expr])
      (binary := by
        intro op a1 a2 ty v1 v2 v ha1 ha2 hop ih1 ih2
        simp [P, eval_simpl_expr])
      (cast := by
        intro a ty v1 v ha hcast ih
        change match eval_simpl_expr (.Ecast a ty) with
          | some v' => v' = v
          | none => True
        simp only [eval_simpl_expr]
        cases h : eval_simpl_expr a with
        | none => simp [h]
        | some v' =>
            have hv : v' = v1 := by simpa [P, h] using ih
            subst v1
            cases hc : sem_cast v' (Clight.typeof a) ty Mem.empty with
            | none => simp [h, hc]
            | some v'' =>
                simp [h, hc]
                exact (sem_cast_deterministic v' (Clight.typeof a) ty m v Mem.empty v'' hcast hc).symm)
      (sizeof_type := by intro ty1 ty; simp [P, eval_simpl_expr])
      (alignof_type := by intro ty1 ty; simp [P, eval_simpl_expr])
      (eval_Elvalue := by
        intro a loc ofs bf v hl hd ih
        simp [P, ih])
      (eval_Evar_local := by intro id loc ty h; rfl)
      (eval_Evar_global := by intro id loc ty h1 h2; rfl)
      (eval_Ederef := by intro a ty loc ofs ha ih; rfl)
      (eval_Efield_struct := by
        intro a id ty loc ofs sid co att delta bf ha ht hc ho ih; rfl)
      (eval_Efield_union := by
        intro a id ty loc ofs uid co att delta bf ha ht hc ho ih; rfl)
      hEval
  simpa [P] using hP

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.Cop

private theorem empty_weak_valid_pointer_false (b : CompCert4Lean.Common.Values.block)
    (ofs : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) :
    CompCert4Lean.Common.Memory.Mem.weak_valid_pointer
      CompCert4Lean.Common.Memory.Mem.empty b ofs = false := by
  simp [CompCert4Lean.Common.Memory.Mem.weak_valid_pointer,
    CompCert4Lean.Common.Memory.Mem.valid_pointer,
    CompCert4Lean.Common.Memory.Mem.empty,
    CompCert4Lean.Common.Memory.Mem.perm_dec,
    CompCert4Lean.Common.Memory.Mem.perm_order'_dec,
    CompCert4Lean.Lib.Maps.PMap.get,
    CompCert4Lean.Lib.Maps.PMap.init,
    CompCert4Lean.Lib.Maps.PTree.get,
    CompCert4Lean.Lib.Maps.PTree.empty]
  constructor <;> rfl

theorem static_bool_val_sound : static_bool_val_soundStatement := by
  intro v t m b h
  cases hc : classify_bool t <;>
    cases v <;>
      simp [bool_val, hc, CompCert4Lean.X86_64.Archi.ptr64] at h ⊢ <;>
    try exact h
  · rw [empty_weak_valid_pointer_false] at h
    simp at h

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem Kseqlist_app : Kseqlist_appStatement := by
  intro sl1 sl2 k
  induction sl1 with
  | nil => rfl
  | cons s sl ih => simp [Kseqlist, ih]

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem step_make_set :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_make_setStatement := by
  intro binary64_certificate binary32_certificate xi p tp hmatch
  intro id a ty m b ofs bf t v e le f k hd hl hty
  have hd' := deref_loc_translated
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp hmatch ty m b ofs bf t v hd
  unfold make_set
  cases hchunk : chunk_for_volatile_type (Clight.typeof a) bf with
  | none =>
      simp only [hchunk]
      have hnone : t = CompCert4Lean.Common.Events.E0 ∧
          Clight.deref_loc ty m b ofs bf v := by
        simpa [← hty, hchunk] using hd'
      have hde : Clight.deref_loc (Clight.typeof a) m b ofs bf v := by
        simpa [hty] using hnone.2
      rw [hnone.1]
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_set
      exact Clight.eval_Elvalue a b ofs bf v hl hde
  | some chunk =>
      simp only [hchunk]
      have hsome : bf = .Full ∧
          CompCert4Lean.Common.Events.volatile_load
            (CompCert4Lean.Common.Globalenvs.Genv.to_senv
              (Clight.globalenv tp).genv_genv)
            chunk m b ofs t v := by
        simpa [← hty, hchunk] using hd'
      rcases hsome with ⟨rfl, hload⟩
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_builtin
      · refine Clight.eval_exprlist.cons
          (a := .Eaddrof a (.Tpointer (Clight.typeof a) Ctypes.noattr))
          (rest := [])
          (ty := .Tpointer (Clight.typeof a) Ctypes.noattr)
          (types := [])
          (v1 := .Vptr b ofs) (v2 := .Vptr b ofs) (values := []) ?_ ?_
          Clight.eval_exprlist.nil
        · exact Clight.eval_Eaddrof a
            (.Tpointer (Clight.typeof a) Ctypes.noattr) b ofs hl
        · simp [Cop.sem_cast, Cop.classify_cast, Clight.typeof,
            CompCert4Lean.X86_64.Archi.ptr64]
      · exact CompCert4Lean.Common.Events.volatile_load_sem_intro _ _ _ _ _ hload

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr

theorem step_make_assign :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_make_assignStatement := by
  intro binary64_certificate binary32_certificate xi p tp hmatch
  intro a1 a2 ty m b ofs bf t v m' v' v2 e le f k hassign hlvalue hrvalue hcast htype
  have hassign' := assign_loc_translated
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp hmatch ty m b ofs bf v t m' v' hassign
  unfold make_assign
  cases hchunk : chunk_for_volatile_type (Clight.typeof a1) bf with
  | none =>
      simp only [hchunk]
      have hnone : t = CompCert4Lean.Common.Events.E0 ∧
          Clight.assign_loc (Clight.globalenv tp).genv_cenv ty m b ofs bf v m' := by
        simpa [← htype, hchunk] using hassign'
      rcases hnone with ⟨ht, hass⟩
      rw [ht]
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_assign
      · exact hlvalue
      · exact hrvalue
      · simpa [htype] using hcast
      · simpa [htype] using hass
  | some chunk =>
      simp only [hchunk]
      have hsome : bf = .Full ∧
          CompCert4Lean.Common.Events.volatile_store
            (CompCert4Lean.Common.Globalenvs.Genv.to_senv
              (Clight.globalenv tp).genv_genv)
            chunk m b ofs v t m' := by
        simpa [← htype, hchunk] using hassign'
      rcases hsome with ⟨rfl, hstore⟩
      change Clight.step
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi
        (Clight.globalenv tp) (Clight.function_entry1 (Clight.globalenv tp)) _ _ _
      apply Clight.step_builtin
      · refine Clight.eval_exprlist.cons
          (a := .Eaddrof a1 (.Tpointer (Clight.typeof a1) Ctypes.noattr))
          (rest := [a2])
          (ty := .Tpointer (Clight.typeof a1) Ctypes.noattr)
          (types := [Clight.typeof a1])
          (v1 := .Vptr b ofs) (v2 := .Vptr b ofs) (values := [v]) ?_ ?_ ?_
        · exact Clight.eval_Eaddrof a1
            (.Tpointer (Clight.typeof a1) Ctypes.noattr) b ofs hlvalue
        · simp [Cop.sem_cast, Cop.classify_cast, Clight.typeof,
            CompCert4Lean.X86_64.Archi.ptr64]
        · refine Clight.eval_exprlist.cons
            (a := a2) (rest := [])
            (ty := Clight.typeof a1) (types := [])
            (v1 := v2) (v2 := v) (values := []) ?_ ?_
            Clight.eval_exprlist.nil
          · exact hrvalue
          · simpa [htype] using hcast
      · exact CompCert4Lean.Common.Events.volatile_store_sem_intro _ _ _ _ _ _ hstore

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events

theorem push_seq :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      push_seqStatement := by
  intro binary64_certificate binary32_certificate
  intro xi tp f sl k e le m
  have aux :
      ∀ (seed : Clight.statement) (sl : List Clight.statement) (k : Clight.cont),
        star (Clight.step1 xi) (Clight.globalenv tp)
          (Clight.State f (SimplExpr.makeseq_rec seed sl) k e le m) E0
          (Clight.State f seed (Kseqlist sl k) e le m) := by
    intro seed sl
    revert seed
    induction sl with
    | nil =>
        intro seed k
        apply star_refl
    | cons s rest ih =>
        intro seed k
        simp only [SimplExpr.makeseq_rec, Kseqlist]
        refine @CompCert4Lean.Common.Smallstep.star_right _ _ _ _ _ E0
          (Clight.State f (.Ssequence seed s) (Kseqlist rest k) e le m) E0 _ E0 ?_ ?_ ?_
        · exact ih (.Ssequence seed s) k
        · exact Clight.step.step_seq f seed s (Kseqlist rest k) e le m
        · rfl
  simpa [SimplExpr.makeseq] using aux Clight.Sskip sl k
      
end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Lib.Maps

theorem step_tr_rvalof :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_tr_rvalofStatement := by
  intro binary64_certificate binary32_certificate xi p tp hmatch
  intro cu hlink ty m b ofs bf t v e le a sl a' tmp f k hderef hlvalue htr htype
  cases htr with
  | tr_rvalof_nonvol _ hvolatile =>
      have hderef_translated := deref_loc_translated
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        p tp hmatch ty m b ofs bf t v hderef
      have hnonvol : t = CompCert4Lean.Common.Events.E0 ∧
          Clight.deref_loc ty m b ofs bf v := by
        simpa [chunk_for_volatile_type, hvolatile] using hderef_translated
      rcases hnonvol with ⟨rfl, hderef_clight⟩
      refine ⟨le, ?_, ?_, rfl, ?_⟩
      · apply star_refl
      · exact Clight.eval_expr.eval_Elvalue a b ofs bf v hlvalue
          (by simpa [htype] using hderef_clight)
      · intro x hx
        rfl
  | tr_rvalof_vol id bf' _ hvolatile htmp haccess =>
      have hbf : bf' = bf := is_bitfield_access_sound
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        p tp hmatch cu hlink e le m a b ofs bf bf' hlvalue haccess
      subst bf'
      refine ⟨PTree.set id v le, ?_, ?_, htype.symm, ?_⟩
      · simp only [Kseqlist]
        apply star_two
        · exact Clight.step_skip_seq f (make_set bf id a) k e le m
        · exact step_make_set
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi p tp hmatch id a ty m b ofs bf t v e le f k hderef hlvalue htype
        · rfl
      · exact Clight.eval_expr.eval_Etempvar id ty v (PTree.gss id v le)
      · intro x hx
        apply PTree.gso
        intro heq
        subst x
        exact hx htmp

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem match_cont_is_call_cont :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      match_cont_is_call_contStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp ce k tk hmatch hcall ce'
  cases hmatch <;> simp [Csem.is_call_cont] at hcall ⊢ <;>
    try contradiction
  all_goals
    constructor <;> assumption

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem match_cont_call_cont :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      match_cont_call_contStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp ce k tk hmatch
  induction hmatch using match_cont.rec
      (motive_2 := fun _ _ _ _ _ _ => True) with
  | match_Kstop ce =>
      intro ce'
      simp [Csem.call_cont, Clight.call_cont]
      exact match_cont.match_Kstop ce'
  | @match_Kseq ce s k ts tk hstmt hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kwhile2 ce r s k s' ts tk hr hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kdowhile1 ce r s k s' ts tk hr hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kfor3 ce r s3 s k ts3 s' ts tk hr hs3 hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kfor4 ce r s3 s k ts3 s' ts tk hr hs3 hs hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kswitch2 ce k tk hk ih =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using ih ce'
  | @match_Kcall f e C ty k optid tf le sl tk a dest tmps cu ce hlink htrf hctx htr hmc =>
      intro ce'
      simpa [Csem.call_cont, Clight.call_cont] using
        (match_cont.match_Kcall (prog := p) (tprog := tp)
          f e C ty k optid tf le sl tk a dest tmps cu ce'
          hlink htrf hctx htr hmc)
  | match_Kdo => exact True.intro
  | match_Kifthenelse_empty => exact True.intro
  | match_Kifthenelse_1 => exact True.intro
  | match_Kwhile1 => exact True.intro
  | match_Kdowhile2 => exact True.intro
  | match_Kfor2 => exact True.intro
  | match_Kswitch1 => exact True.intro
  | match_Kreturn => exact True.intro

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_select_switch :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_select_switchStatement := by
  intro binary64_certificate binary32_certificate ce
  have hdefault : ∀ ls tls,
      tr_lblstmts ce ls tls →
      tr_lblstmts ce (Csem.select_switch_default ls)
        (Clight.select_switch_default tls) := by
    intro ls tls htr
    induction htr using tr_lblstmts.rec
        (motive_1 := fun _ _ _ => True) <;> try trivial
    case tr_ls_nil => exact tr_lblstmts.tr_ls_nil
    case tr_ls_cons c s ls ts tls hs hls ihs ih =>
      cases c with
      | none => exact tr_lblstmts.tr_ls_cons none s ls ts tls hs hls
      | some z => exact ih
  have hcase : ∀ n ls tls,
      tr_lblstmts ce ls tls →
      match Csem.select_switch_case n ls with
      | none => Clight.select_switch_case n tls = none
      | some ls' => ∃ tls', Clight.select_switch_case n tls = some tls' ∧
          tr_lblstmts ce ls' tls' := by
    intro n ls tls htr
    induction htr using tr_lblstmts.rec
        (motive_1 := fun _ _ _ => True) <;> try trivial
    case tr_ls_cons c s ls ts tls hs hls ihs ih =>
      cases c with
      | none => exact ih
      | some z =>
          simp only [Csem.select_switch_case, Clight.select_switch_case]
          cases hz : CompCert4Lean.Lib.Coqlib.zeq z n with
          | left heq =>
              exact ⟨Clight.LScons (some z) ts tls, rfl,
                tr_lblstmts.tr_ls_cons (some z) s ls ts tls hs hls⟩
          | right hne => exact ih
  intro n ls tls htr
  unfold Csem.select_switch Clight.select_switch
  have hinfo := hcase n ls tls htr
  cases hsel : Csem.select_switch_case n ls with
  | some ls' =>
      rw [hsel] at hinfo
      rcases hinfo with ⟨tls', htls, hselected⟩
      rw [htls]
      exact hselected
  | none =>
      rw [hsel] at hinfo
      rw [hinfo]
      exact hdefault ls tls htr

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_seq_of_labeled_statement :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_seq_of_labeled_statementStatement := by
  intro binary64_certificate binary32_certificate ce ls tls htr
  induction htr using tr_lblstmts.rec
      (motive_1 := fun _ _ _ => True) <;> try trivial
  case tr_ls_nil => exact tr_stmt.tr_skip
  case tr_ls_cons c s ls ts tls hs hls ihs ih =>
    exact tr_stmt.tr_seq s (Csem.seq_of_labeled_statement ls)
      ts (Clight.seq_of_labeled_statement tls) hs ih

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

private def pgNoLabel (s : Clight.statement) : Prop :=
  ∀ lbl k, Clight.find_label lbl s k = none

private def pgNoLabelList (sl : List Clight.statement) : Prop :=
  ∀ s, s ∈ sl → pgNoLabel s

private theorem pgNoLabel_sequence {s1 s2 : Clight.statement}
    (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) :
    pgNoLabel (.Ssequence s1 s2) := by
  intro lbl k
  simp only [Clight.find_label]
  rw [h1 lbl (.Kseq s2 k)]
  exact h2 lbl k

private theorem pgNoLabel_ifthenelse {a : Clight.expr}
    {s1 s2 : Clight.statement} (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) :
    pgNoLabel (.Sifthenelse a s1 s2) := by
  intro lbl k
  simp only [Clight.find_label]
  rw [h1 lbl k]
  exact h2 lbl k

private theorem pgNoLabel_makeif
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] {a : Clight.expr}
    {s1 s2 : Clight.statement} (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) :
    pgNoLabel (SimplExpr.makeif a s1 s2) := by
  cases heval : SimplExpr.eval_simpl_expr a with
  | none =>
      simpa [SimplExpr.makeif, heval] using pgNoLabel_ifthenelse h1 h2
  | some v =>
      cases hbool : Cop.bool_val v (Clight.typeof a)
          CompCert4Lean.Common.Memory.Mem.empty with
      | none =>
          simpa [SimplExpr.makeif, heval, hbool] using pgNoLabel_ifthenelse h1 h2
      | some b =>
          cases b <;> simp [SimplExpr.makeif, heval, hbool, h1, h2]

private theorem pgNoLabel_make_set (bf : bitfield) (id : ident)
    (a : Clight.expr) : pgNoLabel (SimplExpr.make_set bf id a) := by
  unfold SimplExpr.make_set
  cases SimplExpr.chunk_for_volatile_type (Clight.typeof a) bf <;>
    intro lbl k <;> rfl

private theorem pgNoLabel_make_assign (bf : bitfield) (a1 a2 : Clight.expr) :
    pgNoLabel (SimplExpr.make_assign bf a1 a2) := by
  unfold SimplExpr.make_assign
  cases SimplExpr.chunk_for_volatile_type (Clight.typeof a1) bf <;>
    intro lbl k <;> rfl

private theorem pgNoLabelList_do_set (sd : SimplExpr.set_destination)
    (a : Clight.expr) : pgNoLabelList (SimplExpr.do_set sd a) := by
  induction sd generalizing a with
  | SDbase =>
      intro s hs
      simp only [SimplExpr.do_set, List.mem_singleton] at hs
      subst s
      intro lbl k
      rfl
  | SDcons tycast ty tmp sd ih =>
      intro s hs
      simp only [SimplExpr.do_set, List.mem_cons] at hs
      rcases hs with rfl | hs
      · intro lbl k
        rfl
      · exact ih _ _ hs

private theorem pgNoLabelList_final (dst : SimplExpr.destination)
    (a : Clight.expr) : pgNoLabelList (SimplExprspec.final dst a) := by
  cases dst with
  | For_val => simp [SimplExprspec.final, pgNoLabelList]
  | For_effects => simp [SimplExprspec.final, pgNoLabelList]
  | For_set sd => exact pgNoLabelList_do_set sd a

private theorem pgNoLabelList_rvalof {ce : composite_env} {ty : Ctypes.type}
    {a : Clight.expr} {sl : List Clight.statement} {a' : Clight.expr}
    {tmp : List ident} (h : SimplExprspec.tr_rvalof ce ty a sl a' tmp) :
    pgNoLabelList sl := by
  cases h with
  | tr_rvalof_nonvol => simp [pgNoLabelList]
  | tr_rvalof_vol =>
      intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact pgNoLabel_make_set _ _ _

private theorem pgNoLabel_makeseq_rec (s : Clight.statement)
    (hs : pgNoLabel s) (sl : List Clight.statement)
    (hsl : pgNoLabelList sl) : pgNoLabel (SimplExpr.makeseq_rec s sl) := by
  induction sl generalizing s with
  | nil => simpa [SimplExpr.makeseq_rec]
  | cons s' sl ih =>
      apply ih (.Ssequence s s') (pgNoLabel_sequence hs (hsl s' (by simp)))
      intro s'' hs''
      exact hsl s'' (by simp [hs''])

private theorem pgNoLabel_makeseq (sl : List Clight.statement)
    (hsl : pgNoLabelList sl) : pgNoLabel (SimplExpr.makeseq sl) := by
  apply pgNoLabel_makeseq_rec .Sskip
  · intro lbl k
    rfl
  · exact hsl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

private theorem pgNoLabel_skip : pgNoLabel Clight.Sskip := by
  intro lbl k
  rfl

private theorem pgNoLabel_assign (a1 a2 : Clight.expr) :
    pgNoLabel (.Sassign a1 a2) := by
  intro lbl k
  rfl

private theorem pgNoLabel_set (id : ident) (a : Clight.expr) :
    pgNoLabel (.Sset id a) := by
  intro lbl k
  rfl

private theorem pgNoLabel_call (id : Option ident) (a : Clight.expr)
    (args : List Clight.expr) : pgNoLabel (.Scall id a args) := by
  intro lbl k
  rfl

private theorem pgNoLabel_builtin (id : Option ident)
    (ef : CompCert4Lean.Common.AST.external_function) (tys : List Ctypes.type)
    (args : List Clight.expr) : pgNoLabel (.Sbuiltin id ef tys args) := by
  intro lbl k
  rfl

private theorem pgNoLabelList_nil : pgNoLabelList [] := by
  intro s hs
  simp at hs

private theorem pgNoLabelList_cons (s : Clight.statement)
    (sl : List Clight.statement) :
    pgNoLabelList (s :: sl) ↔ pgNoLabel s ∧ pgNoLabelList sl := by
  constructor
  · intro h
    constructor
    · exact h s (by simp)
    · intro s' hs'
      exact h s' (by simp [hs'])
  · rintro ⟨hs, hsl⟩ s' hs'
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · exact hs
    · exact hsl s' hs'

private theorem pgNoLabelList_append (sl1 sl2 : List Clight.statement) :
    pgNoLabelList (sl1 ++ sl2) ↔ pgNoLabelList sl1 ∧ pgNoLabelList sl2 := by
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (List.mem_append_left sl2 hs)
    · intro s hs
      exact h s (List.mem_append_right sl1 hs)
  · rintro ⟨h1, h2⟩ s hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · exact h1 s hs
    · exact h2 s hs

private theorem pgTrExprNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {ce : composite_env} {le : Clight.temp_env} {dst : SimplExpr.destination}
    {r : cexpr} {sl : List Clight.statement} {a : Clight.expr}
    {tmps : List ident} (h : SimplExprspec.tr_expr ce le dst r sl a tmps) :
    pgNoLabelList sl := by
  let P1 := fun (_dst : SimplExpr.destination) (_r : cexpr)
      (sl : List Clight.statement) (_a : Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_expr ce le _dst _r sl _a _tmps) =>
      pgNoLabelList sl
  let P2 := fun (_rl : cexprlist) (sl : List Clight.statement)
      (_al : List Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_exprlist ce le _rl sl _al _tmps) =>
      pgNoLabelList sl
  refine SimplExprspec.tr_expr.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2] at * <;>
      simp_all [pgNoLabelList_nil, pgNoLabelList_cons,
        pgNoLabelList_append, pgNoLabelList_final, pgNoLabelList_do_set,
        pgNoLabelList_rvalof, pgNoLabel_make_assign, pgNoLabel_make_set,
        pgNoLabel_makeif, pgNoLabel_makeseq, pgNoLabel_skip,
        pgNoLabel_assign, pgNoLabel_set, pgNoLabel_call, pgNoLabel_builtin]
  all_goals
    apply pgNoLabelList_rvalof
    assumption

private theorem pgTrExprListNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {ce : composite_env} {le : Clight.temp_env} {rl : cexprlist}
    {sl : List Clight.statement} {al : List Clight.expr} {tmps : List ident}
    (h : SimplExprspec.tr_exprlist ce le rl sl al tmps) :
    pgNoLabelList sl := by
  let P1 := fun (_dst : SimplExpr.destination) (_r : cexpr)
      (sl : List Clight.statement) (_a : Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_expr ce le _dst _r sl _a _tmps) =>
      pgNoLabelList sl
  let P2 := fun (_rl : cexprlist) (sl : List Clight.statement)
      (_al : List Clight.expr) (_tmps : List ident)
      (_ : SimplExprspec.tr_exprlist ce le _rl sl _al _tmps) =>
      pgNoLabelList sl
  refine SimplExprspec.tr_exprlist.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals
    intros <;> dsimp [P1, P2] at * <;>
      simp_all [pgNoLabelList_nil, pgNoLabelList_cons,
        pgNoLabelList_append, pgNoLabelList_final, pgNoLabelList_do_set,
        pgNoLabelList_rvalof, pgNoLabel_make_assign, pgNoLabel_make_set,
        pgNoLabel_makeif, pgNoLabel_makeseq, pgNoLabel_skip,
        pgNoLabel_assign, pgNoLabel_set, pgNoLabel_call, pgNoLabel_builtin]
  all_goals
    apply pgNoLabelList_rvalof
    assumption

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

private theorem pgTrTopNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    {ce : composite_env} {ge : Clight.genv} {e : Clight.env}
    {le : Clight.temp_env} {m : mem} {dst : SimplExpr.destination}
    {r : cexpr} {sl : List Clight.statement} {a : Clight.expr}
    {tmps : List ident} (h : SimplExprspec.tr_top ce ge e le m dst r sl a tmps) :
    pgNoLabelList sl := by
  cases h with
  | tr_top_val_val => exact pgNoLabelList_nil
  | tr_top_base _ _ _ _ _ htr => exact pgTrExprNoLabel htr

private theorem pgTrExpressionNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (tp : tprogram) {ce : composite_env} {r : cexpr}
    {s : Clight.statement} {a : Clight.expr}
    (h : SimplExprspec.tr_expression ce r s a) : pgNoLabel s := by
  cases h with
  | tr_expression_intro sl a tmps htop =>
      apply pgNoLabel_makeseq
      apply pgTrTopNoLabel
      exact htop (Clight.globalenv tp) Clight.empty_env
        (CompCert4Lean.Lib.Maps.PTree.empty val)
        CompCert4Lean.Common.Memory.Mem.empty

private theorem pgTrExprStmtNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (tp : tprogram) {ce : composite_env} {r : cexpr}
    {s : Clight.statement} (h : SimplExprspec.tr_expr_stmt ce r s) :
    pgNoLabel s := by
  cases h with
  | tr_expr_stmt_intro sl a tmps htop =>
      apply pgNoLabel_makeseq
      apply pgTrTopNoLabel
      exact htop (Clight.globalenv tp) Clight.empty_env
        (CompCert4Lean.Lib.Maps.PTree.empty val)
        CompCert4Lean.Common.Memory.Mem.empty

private theorem pgTrIfNoLabel
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (tp : tprogram) {ce : composite_env} {r : cexpr}
    {s1 s2 ts : Clight.statement} (h : SimplExprspec.tr_if ce r s1 s2 ts)
    (h1 : pgNoLabel s1) (h2 : pgNoLabel s2) : pgNoLabel ts := by
  cases h with
  | tr_if_intro sl a tmps htop =>
      apply pgNoLabel_makeseq
      rw [pgNoLabelList_append]
      constructor
      · apply pgTrTopNoLabel
        exact htop (Clight.globalenv tp) Clight.empty_env
          (CompCert4Lean.Lib.Maps.PTree.empty val)
          CompCert4Lean.Common.Memory.Mem.empty
      · rw [pgNoLabelList_cons]
        exact ⟨pgNoLabel_makeif h1 h2, pgNoLabelList_nil⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExprspec

theorem tr_find_label :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_find_labelStatement := by
  intro binary64_certificate binary32_certificate p tp ce lbl s k ts tk htr hmc
  let P1 := fun (s : cstatement)
      (ts : Clight.statement) (_ : tr_stmt ce s ts) =>
      ∀ lbl k tk, match_cont p tp ce k tk →
        match Csem.find_label lbl s k with
        | none => Clight.find_label lbl ts tk = none
        | some (s', k') =>
            ∃ ts' tk', Clight.find_label lbl ts tk = some (ts', tk') ∧
              tr_stmt ce s' ts' ∧ match_cont p tp ce k' tk'
  let P2 := fun (s : clabeled_statements)
      (ts : Clight.labeled_statements) (_ : tr_lblstmts ce s ts) =>
      ∀ lbl k tk, match_cont p tp ce k tk →
        match Csem.find_label_ls lbl s k with
        | none => Clight.find_label_ls lbl ts tk = none
        | some (s', k') =>
            ∃ ts' tk', Clight.find_label_ls lbl ts tk = some (ts', tk') ∧
              tr_stmt ce s' ts' ∧ match_cont p tp ce k' tk'
  refine (SimplExprspec.tr_stmt.rec (motive_1 := P1) (motive_2 := P2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htr) lbl k tk hmc
  · intro lbl k tk hmc
    rfl
  · intro r s h lbl k tk hmc
    exact pgTrExprStmtNoLabel tp h lbl tk
  · intro s1 s2 ts1 ts2 h1 h2 ih1 ih2 lbl k tk hmc
    have hmc1 : match_cont p tp ce (Csem.Kseq s2 k) (Clight.Kseq ts2 tk) :=
      match_cont.match_Kseq ce s2 k ts2 tk h2 hmc
    have hi1 := ih1 lbl (Csem.Kseq s2 k) (Clight.Kseq ts2 tk) hmc1
    simp only [Csem.find_label, Clight.find_label]
    cases hc : Csem.find_label lbl s1 (Csem.Kseq s2 k) with
    | none =>
        rw [hc] at hi1
        rw [hi1]
        exact ih2 lbl k tk hmc
    | some sk =>
        rcases sk with ⟨s', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s' a h lbl k tk hmc
    change Clight.find_label lbl (.Ssequence s' .Sskip) tk = none
    exact pgNoLabel_sequence (pgTrExpressionNoLabel tp h) pgNoLabel_skip lbl tk
  · intro r s1 s2 s' a ts1 ts2 hr h1 h2 ih1 ih2 lbl k tk hmc
    have hpref := pgTrExpressionNoLabel tp hr
    have hi1 := ih1 lbl k tk hmc
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq (.Sifthenelse a ts1 ts2) tk)]
    simp only [Clight.find_label]
    cases hc : Csem.find_label lbl s1 k with
    | none =>
        rw [hc] at hi1
        rw [hi1]
        exact ih2 lbl k tk hmc
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s1 s' ts1 hr h1 ih1 lbl k tk hmc
    have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
    have hmc1 : match_cont p tp ce (Csem.Kwhile2 r s1 k)
        (Clight.Kloop1 (.Ssequence s' ts1) .Sskip tk) :=
      match_cont.match_Kwhile2 ce r s1 k s' ts1 tk hr h1 hmc
    have hi1 := ih1 lbl (Csem.Kwhile2 r s1 k)
      (Clight.Kloop1 (.Ssequence s' ts1) .Sskip tk) hmc1
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq ts1 (.Kloop1 (.Ssequence s' ts1) .Sskip tk))]
    cases hc : Csem.find_label lbl s1 (Csem.Kwhile2 r s1 k) with
    | none =>
        rw [hc] at hi1
        rw [hi1]
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s1 s' ts1 hr h1 ih1 lbl k tk hmc
    have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
    have hmc1 : match_cont p tp ce (Csem.Kdowhile1 r s1 k)
        (Clight.Kloop1 ts1 s' tk) :=
      match_cont.match_Kdowhile1 ce r s1 k s' ts1 tk hr h1 hmc
    have hi1 := ih1 lbl (Csem.Kdowhile1 r s1 k)
      (Clight.Kloop1 ts1 s' tk) hmc1
    simp only [Csem.find_label, Clight.find_label]
    cases hc : Csem.find_label lbl s1 (Csem.Kdowhile1 r s1 k) with
    | none =>
        rw [hc] at hi1
        rw [hi1]
        exact hpref lbl (Clight.Kloop2 ts1 s' tk)
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc] at hi1
        rcases hi1 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
  · intro r s3 s4 s' ts3 ts4 hr h3 h4 ih3 ih4 lbl k tk hmc
    have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
    have hmc3 : match_cont p tp ce (Csem.Kfor3 r s3 s4 k)
        (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) :=
      match_cont.match_Kfor3 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
    have hi4 := ih4 lbl (Csem.Kfor3 r s3 s4 k)
      (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) hmc3
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq ts4 (.Kloop1 (.Ssequence s' ts4) ts3 tk))]
    cases hc4 : Csem.find_label lbl s4 (Csem.Kfor3 r s3 s4 k) with
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hc4] at hi4
        rcases hi4 with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
    | none =>
        rw [hc4] at hi4
        rw [hi4]
        have hmc4 : match_cont p tp ce (Csem.Kfor4 r s3 s4 k)
            (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) :=
          match_cont.match_Kfor4 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
        exact ih3 lbl (Csem.Kfor4 r s3 s4 k)
          (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) hmc4
  · intro s1 r s3 s4 s' ts1 ts3 ts4 hr hnot h1 h3 h4
      ih1 ih3 ih4 lbl k tk hmc
    let loop : Clight.statement := .Sloop (.Ssequence s' ts4) ts3
    have hfor : tr_stmt ce (.Sfor .Sskip r s3 s4) loop :=
      tr_stmt.tr_for_1 r s3 s4 s' ts3 ts4 hr h3 h4
    have hmci : match_cont p tp ce
        (Csem.Kseq (.Sfor .Sskip r s3 s4) k) (Clight.Kseq loop tk) :=
      match_cont.match_Kseq ce (.Sfor .Sskip r s3 s4) k loop tk hfor hmc
    have hii := ih1 lbl (Csem.Kseq (.Sfor .Sskip r s3 s4) k)
      (Clight.Kseq loop tk) hmci
    simp only [Csem.find_label, Clight.find_label]
    cases hci : Csem.find_label lbl s1
        (Csem.Kseq (.Sfor .Sskip r s3 s4) k) with
    | some sk =>
        rcases sk with ⟨s'', k'⟩
        rw [hci] at hii
        rcases hii with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩
    | none =>
        rw [hci] at hii
        rw [hii]
        have hpref := pgTrIfNoLabel tp hr pgNoLabel_skip (by intro l k; rfl)
        rw [hpref lbl (.Kseq ts4 (.Kloop1 (.Ssequence s' ts4) ts3 tk))]
        have hmc3 : match_cont p tp ce (Csem.Kfor3 r s3 s4 k)
            (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) :=
          match_cont.match_Kfor3 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
        have hi4 := ih4 lbl (Csem.Kfor3 r s3 s4 k)
          (Clight.Kloop1 (.Ssequence s' ts4) ts3 tk) hmc3
        cases hc4 : Csem.find_label lbl s4 (Csem.Kfor3 r s3 s4 k) with
        | some sk =>
            rcases sk with ⟨s'', k'⟩
            rw [hc4] at hi4
            rcases hi4 with ⟨ts', tk', heq, htr', hmc'⟩
            rw [heq]
            exact ⟨ts', tk', rfl, htr', hmc'⟩
        | none =>
            rw [hc4] at hi4
            rw [hi4]
            have hmc4 : match_cont p tp ce (Csem.Kfor4 r s3 s4 k)
                (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) :=
              match_cont.match_Kfor4 ce r s3 s4 k ts3 s' ts4 tk hr h3 h4 hmc
            exact ih3 lbl (Csem.Kfor4 r s3 s4 k)
              (Clight.Kloop2 (.Ssequence s' ts4) ts3 tk) hmc4
  · intro lbl k tk hmc
    rfl
  · intro lbl k tk hmc
    rfl
  · intro lbl k tk hmc
    rfl
  · intro r s' a h lbl k tk hmc
    change Clight.find_label lbl (.Ssequence s' (.Sreturn (some a))) tk = none
    exact pgNoLabel_sequence (pgTrExpressionNoLabel tp h)
      (by intro l k; rfl) lbl tk
  · intro r ls s' a tls hr hls ihls lbl k tk hmc
    have hpref := pgTrExpressionNoLabel tp hr
    simp only [Csem.find_label, Clight.find_label]
    rw [hpref lbl (.Kseq (.Sswitch a tls) tk)]
    have hmcs : match_cont p tp ce (Csem.Kswitch2 k) (Clight.Kswitch tk) :=
      match_cont.match_Kswitch2 ce k tk hmc
    exact ihls lbl (Csem.Kswitch2 k) (Clight.Kswitch tk) hmcs
  · intro label s ts h ih lbl k tk hmc
    simp only [Csem.find_label, Clight.find_label]
    cases heq : CompCert4Lean.Common.AST.ident_eq lbl label with
    | left hsame => exact ⟨ts, tk, rfl, h, hmc⟩
    | right hne => exact ih lbl k tk hmc
  · intro label lbl k tk hmc
    rfl
  · intro lbl k tk hmc
    rfl
  · intro c s ls ts tls hs hls ihs ihls lbl k tk hmc
    have hseq : tr_stmt ce (Csem.seq_of_labeled_statement ls)
        (Clight.seq_of_labeled_statement tls) :=
      tr_seq_of_labeled_statement ce ls tls hls
    have hmc1 : match_cont p tp ce
        (Csem.Kseq (Csem.seq_of_labeled_statement ls) k)
        (Clight.Kseq (Clight.seq_of_labeled_statement tls) tk) :=
      match_cont.match_Kseq ce (Csem.seq_of_labeled_statement ls) k
        (Clight.seq_of_labeled_statement tls) tk hseq hmc
    have his := ihs lbl (Csem.Kseq (Csem.seq_of_labeled_statement ls) k)
      (Clight.Kseq (Clight.seq_of_labeled_statement tls) tk) hmc1
    simp only [Csem.find_label_ls, Clight.find_label_ls]
    cases hc : Csem.find_label lbl s
        (Csem.Kseq (Csem.seq_of_labeled_statement ls) k) with
    | none =>
        rw [hc] at his
        rw [his]
        exact ihls lbl k tk hmc
    | some sk =>
        rcases sk with ⟨s', k'⟩
        rw [hc] at his
        rcases his with ⟨ts', tk', heq, htr', hmc'⟩
        rw [heq]
        exact ⟨ts', tk', rfl, htr', hmc'⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem leftcontext_size : leftcontext_sizeStatement := by
  intro kfrom kto C h
  apply CompCert4Lean.Cfrontend.Cstrategy.leftcontext.rec
    (motive_1 := fun _ C _ =>
      ∀ e1 e2, esize e1 < esize e2 → esize (C e1) < esize (C e2))
    (motive_2 := fun C _ =>
      ∀ e1 e2, esize e1 < esize e2 → esizelist (C e1) < esizelist (C e2))
    (t := h)
  all_goals intros
  all_goals (try simp only [esize, esizelist] at *)
  all_goals (try assumption)
  all_goals (try apply Nat.succ_lt_succ)
  all_goals first
    | solve_by_elim
    | apply Nat.add_lt_add_left; solve_by_elim
    | apply Nat.add_lt_add_right; solve_by_elim

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem tr_val_gen :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_val_genStatement := by
  intro binary64_certificate binary32_certificate
  intro ce le dst v ty a tmp htype heval
  cases dst with
  | For_val =>
      exact SimplExprspec.tr_expr.tr_val_value le v ty a tmp htype heval
  | For_effects =>
      exact SimplExprspec.tr_expr.tr_val_effect le v ty a tmp
  | For_set sd =>
      exact SimplExprspec.tr_expr.tr_val_set le sd v ty a a tmp htype heval

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem alloc_variables_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      alloc_variables_preservedStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp hmatch e m params e' m' halloc
  induction halloc with
  | nil e m =>
      exact Clight.alloc_variables.nil e m
  | cons halloc hrest ih =>
      refine Clight.alloc_variables.cons (hrest := ih) (halloc := ?_)
      rw [comp_env_preserved (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) p tp hmatch]
      exact halloc

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem bind_parameters_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      bind_parameters_preservedStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp hmatch e m params args m' hbind
  induction hbind with
  | nil m =>
      exact Clight.bind_parameters.nil m
  | cons hfind hassign hrest ih =>
      apply Clight.bind_parameters.cons
      · exact hfind
      · cases hassign with
        | value hmode hvol hstore =>
            exact Clight.assign_loc_value _ _ _ hmode hstore
        | copy hmode hsrcAlign htgtAlign hseparated hload hstore =>
            have henv : (Clight.globalenv tp).genv_cenv =
                (Csem.globalenv p).genv_cenv :=
              comp_env_preserved (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate) p tp hmatch
            rw [henv]
            apply Clight.assign_loc_copy _ _ _ _ hmode
            · intro _
              exact hsrcAlign
            · intro _
              exact htgtAlign
            · exact hseparated
            · exact hload
            · exact hstore
        | volatile hmode hvol hstore =>
            cases hstore with
            | volatile_store_nonvol a b c d =>
                exact Clight.assign_loc_value _ _ _ hmode d
      · exact ih

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem tr_top_val_for_val_inv :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_top_val_for_val_invStatement := by
  intro binary64_certificate binary32_certificate
  intro tp ce e le m v ty sl a tmps h
  cases h with
  | tr_top_val_val v ty a tmps htype heval =>
      exact ⟨rfl, htype, heval⟩
  | tr_top_base dst r sl a tmps htr =>
      cases htr with
      | tr_val_value v ty a tmps htype heval =>
          exact ⟨rfl, htype, heval _ _ _ _ (by intros; rfl)⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem blocks_of_env_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      blocks_of_env_preservedStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp hmatch e
  unfold Clight.blocks_of_env Csem.blocks_of_env
  unfold Clight.block_of_binding Csem.block_of_binding
  rw [comp_env_preserved (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) p tp hmatch]

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem transl_final_states :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      transl_final_statesStatement := by
  intro binary64_certificate binary32_certificate
  intro p tp S S' r hmatch hfinal
  cases hfinal with
  | intro r m =>
      cases hmatch with
      | match_returnstates res k m tk hmc =>
          have htk := hmc (CompCert4Lean.Lib.Maps.PTree.empty _)
          cases htk
          exact Clight.final_state.intro r m

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem pg3898_globvar_eq {V : Type} {v tv : globvar V}
    (h : match_globvar Eq v tv) : v = tv := by
  cases h with
  | match_globvar_intro i j init ro vo hij => cases hij; rfl

private theorem pg3898_glob_mono {C F G V : Type} [LC : Linker C]
    (R : C → F → G → Prop) {c d : C} {g : globdef F V} {tg : globdef G V}
    (h : match_globdef R Eq c g tg) (hcd : LC.linkorder c d) :
    match_globdef R Eq d g tg := by
  cases h with
  | match_globdef_fun c' f tf hc hr =>
      exact match_globdef_fun R Eq d c' f tf
        (LC.linkorder_trans _ _ _ hc hcd) hr
  | match_globdef_var v tv hv => exact match_globdef_var R Eq d v tv hv

private theorem pg3898_link_glob {C F G V : Type}
    [LC : Linker C] [LF : Linker F] [LG : Linker G] [LV : Linker V]
    (R : C → F → G → Prop)
    (hf : ∀ c1 c2 f1 tf1 f2 tf2 f,
      LF.link f1 f2 = some f → R c1 f1 tf1 → R c2 f2 tf2 →
      ∃ tf, LG.link tf1 tf2 = some tf ∧ (R c1 f tf ∨ R c2 f tf))
    {c1 c2 c : C} {g1 g2 g : globdef F V} {tg1 tg2 : globdef G V}
    (hc1 : LC.linkorder c1 c) (hc2 : LC.linkorder c2 c)
    (hl : link_def g1 g2 = some g)
    (h1 : match_globdef R Eq c1 g1 tg1)
    (h2 : match_globdef R Eq c2 g2 tg2) :
    ∃ tg, link_def tg1 tg2 = some tg ∧ match_globdef R Eq c g tg := by
  cases h1 with
  | match_globdef_fun u1 f1 tf1 hu1 hr1 =>
    cases h2 with
    | match_globdef_var v tv hv => simp [link_def] at hl
    | match_globdef_fun u2 f2 tf2 hu2 hr2 =>
      cases heq : LF.link f1 f2 with
      | none => simp [link_def, heq] at hl
      | some f =>
        simp only [link_def, heq, Option.some.injEq] at hl
        subst g
        obtain ⟨tf, ht, hr⟩ := hf u1 u2 f1 tf1 f2 tf2 f heq hr1 hr2
        refine ⟨.Gfun tf, by simp [link_def, ht], ?_⟩
        cases hr with
        | inl hr =>
            exact match_globdef_fun R Eq c u1 f tf
              (LC.linkorder_trans _ _ _ hu1 hc1) hr
        | inr hr =>
            exact match_globdef_fun R Eq c u2 f tf
              (LC.linkorder_trans _ _ _ hu2 hc2) hr
  | match_globdef_var v1 tv1 hv1 =>
    cases h2 with
    | match_globdef_fun u2 f2 tf2 hu2 hr2 => simp [link_def] at hl
    | match_globdef_var v2 tv2 hv2 =>
      have e1 := pg3898_globvar_eq hv1
      have e2 := pg3898_globvar_eq hv2
      subst tv1; subst tv2
      cases heq : link_vardef v1 v2 with
      | none => simp [link_def, heq] at hl
      | some v =>
        simp only [link_def, heq, Option.some.injEq] at hl
        subst g
        refine ⟨.Gvar v, by simp [link_def, heq], ?_⟩
        apply match_globdef_var
        cases v
        exact match_globvar_intro Eq _ _ _ _ _ rfl

private theorem pg3898_link_succeeds {F V : Type} [LF : Linker F] [LV : Linker V]
    (p1 p2 : CompCert4Lean.Common.AST.program F V)
    (hm : p1.prog_main = p2.prog_main)
    (hc : ∀ id g1 g2, PTree.get id (prog_defmap p1) = some g1 →
      PTree.get id (prog_defmap p2) = some g2 →
      id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧ ∃ g, link_def g1 g2 = some g) :
    link_prog p1 p2 = some {
      prog_defs := PTree.elements (PTree.combine link_prog_merge (prog_defmap p1) (prog_defmap p2))
      prog_public := p1.prog_public ++ p2.prog_public
      prog_main := p1.prog_main } := by
  have hall : PTree_Properties.for_all (prog_defmap p1) (link_prog_check p1 p2) = true := by
    apply (PTree_Properties.for_all_correct_proof _ _ _).mpr
    intro id g1 hget1
    unfold link_prog_check
    cases hget2 : PTree.get id (prog_defmap p2) with
    | none => rfl
    | some g2 =>
      obtain ⟨hp1, hp2, g, hg⟩ := hc id g1 g2 hget1 hget2
      cases hd1 : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec peq id p1.prog_public with
      | right hn => exact (hn hp1).elim
      | left _ =>
        cases hd2 : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec peq id p2.prog_public with
        | right hn => exact (hn hp2).elim
        | left _ => simp [hg]
  unfold link_prog
  cases hd : ident_eq p1.prog_main p2.prog_main with
  | right hn => exact (hn hm).elim
  | left _ => simp only [hall, ite_true]

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem pg3898_option_right {A B : Type} {R : A → B → Prop}
    {o : Option A} {b : B} (h : option_rel R o (some b)) :
    ∃ a, o = some a ∧ R a b := by
  cases h with
  | some a b hr => exact ⟨a, rfl, hr⟩

private theorem pg3898_merge_related {A B : Type}
    (r1 r2 r : A → B → Prop)
    (f : Option A → Option A → Option A)
    (tf : Option B → Option B → Option B)
    (hnn : f none none = none) (htnn : tf none none = none)
    (hnl : ∀ a, f (some a) none = some a)
    (htnl : ∀ b, tf (some b) none = some b)
    (hnr : ∀ a, f none (some a) = some a)
    (htnr : ∀ b, tf none (some b) = some b)
    (hm1 : ∀ a b, r1 a b → r a b) (hm2 : ∀ a b, r2 a b → r a b)
    {o1 o2 : Option A} {t1 t2 : Option B}
    (h1 : option_rel r1 o1 t1) (h2 : option_rel r2 o2 t2)
    (hl : ∀ a b x y, o1 = some a → o2 = some b → r1 a x → r2 b y →
      option_rel r (f (some a) (some b)) (tf (some x) (some y))) :
    option_rel r (f o1 o2) (tf t1 t2) := by
  cases h1 with
  | none =>
    cases h2 with
    | none => rw [hnn, htnn]; exact option_rel.none r
    | some b y hr => rw [hnr, htnr]; exact option_rel.some b y (hm2 b y hr)
  | some a x hr =>
    cases h2 with
    | none => rw [hnl, htnl]; exact option_rel.some a x (hm1 a x hr)
    | some b y hr' => exact hl a b x y rfl rfl hr hr'

private theorem pg3898_link_ast {C F G V : Type}
    [LC : Linker C] [LF : Linker F] [LG : Linker G] [LV : Linker V]
    (R : C → F → G → Prop)
    (hf : ∀ c1 c2 f1 tf1 f2 tf2 f,
      LF.link f1 f2 = some f → R c1 f1 tf1 → R c2 f2 tf2 →
      ∃ tf, LG.link tf1 tf2 = some tf ∧ (R c1 f tf ∨ R c2 f tf))
    (c1 c2 c : C)
    (p1 p2 : CompCert4Lean.Common.AST.program F V)
    (tp1 tp2 : CompCert4Lean.Common.AST.program G V)
    (p : CompCert4Lean.Common.AST.program F V)
    (hl : link_prog p1 p2 = some p)
    (h1 : match_program_gen R Eq c1 p1 tp1)
    (h2 : match_program_gen R Eq c2 p2 tp2)
    (hc1 : LC.linkorder c1 c) (hc2 : LC.linkorder c2 c) :
    ∃ tp, link_prog tp1 tp2 = some tp ∧ match_program_gen R Eq c p tp := by
  obtain ⟨hmain, hcompat, hp⟩ := link_prog_inv_proof p1 p2 p hl
  have hd1 := match_program_defmap R Eq c1 p1 tp1 h1
  have hd2 := match_program_defmap R Eq c2 p2 tp2 h2
  let tp : CompCert4Lean.Common.AST.program G V := {
    prog_defs := PTree.elements
      (PTree.combine link_prog_merge (prog_defmap tp1) (prog_defmap tp2))
    prog_public := tp1.prog_public ++ tp2.prog_public
    prog_main := tp1.prog_main }
  refine ⟨tp, ?_, ?_⟩
  · apply pg3898_link_succeeds
    · exact h1.2.1.trans (hmain.trans h2.2.1.symm)
    · intro id tg1 tg2 ht1 ht2
      have hm1 := hd1 id
      have hm2 := hd2 id
      rw [ht1] at hm1
      rw [ht2] at hm2
      obtain ⟨g1, hg1, hr1⟩ := pg3898_option_right hm1
      obtain ⟨g2, hg2, hr2⟩ := pg3898_option_right hm2
      obtain ⟨hpub1, hpub2, g, hg⟩ := hcompat id g1 g2 hg1 hg2
      obtain ⟨tg, htg, _⟩ := pg3898_link_glob R hf hc1 hc2 hg hr1 hr2
      exact ⟨h1.2.2.symm ▸ hpub1, h2.2.2.symm ▸ hpub2, tg, htg⟩
  · constructor
    · rw [hp]
      apply PTree.elements_canonical_order'
      intro id
      rw [PTree.gcombine_proof (f := link_prog_merge) (by rfl),
        PTree.gcombine_proof (f := link_prog_merge) (by rfl)]
      apply pg3898_merge_related
        (match_globdef R Eq c1) (match_globdef R Eq c2) (match_globdef R Eq c)
        link_prog_merge link_prog_merge rfl rfl
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ hr => pg3898_glob_mono R hr hc1)
        (fun _ _ hr => pg3898_glob_mono R hr hc2) (hd1 id) (hd2 id)
      intro g1 g2 tg1 tg2 hg1 hg2 hr1 hr2
      obtain ⟨_, _, g, hg⟩ := hcompat id g1 g2 hg1 hg2
      obtain ⟨tg, htg, hr⟩ := pg3898_link_glob R hf hc1 hc2 hg hr1 hr2
      simp only [link_prog_merge, hg, htg]
      exact option_rel.some g tg hr
    · rw [hp]
      exact ⟨h1.2.1, by simp only [tp, h1.2.2, h2.2.2]⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Coqlib

private theorem pg3898_link_fundef
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (c1 c2 : cprogram) (f1 : cfundef) (tf1 : tfundef) (f2 : cfundef) (tf2 : tfundef)
    (f : cfundef) (hl : Ctypes.link_fundef f1 f2 = some f)
    (h1 : tr_fundef c1 f1 tf1) (h2 : tr_fundef c2 f2 tf2) :
    ∃ tf, Ctypes.link_fundef tf1 tf2 = some tf ∧
      (tr_fundef c1 f tf ∨ tr_fundef c2 f tf) := by
  cases h1 with
  | tr_internal f1 tf1 hfn1 =>
    cases h2 with
    | tr_internal f2 tf2 hfn2 => simp [Ctypes.link_fundef] at hl
    | tr_external ef args res cc =>
      cases ef <;> simp [Ctypes.link_fundef] at hl
      case EF_external id sg =>
        cases Option.some.inj hl
        exact ⟨.Internal tf1, rfl, Or.inl (tr_fundef.tr_internal _ _ hfn1)⟩
  | tr_external ef1 args1 res1 cc1 =>
    cases h2 with
    | tr_internal f2 tf2 hfn2 =>
      cases ef1 <;> simp [Ctypes.link_fundef] at hl
      case EF_external id sg =>
        cases Option.some.inj hl
        exact ⟨.Internal tf2, rfl, Or.inr (tr_fundef.tr_internal _ _ hfn2)⟩
    | tr_external ef2 args2 res2 cc2 =>
      cases he : external_function_eq ef1 ef2 with
      | right _ => simp [Ctypes.link_fundef, he] at hl
      | left _ =>
        cases ha : Ctypes.typelist_eq args1 args2 with
        | right _ => simp [Ctypes.link_fundef, he, ha] at hl
        | left _ =>
          cases hr : Ctypes.type_eq res1 res2 with
          | right _ => simp [Ctypes.link_fundef, he, ha, hr] at hl
          | left _ =>
            cases hc : calling_convention_eq cc1 cc2 with
            | right _ => simp [Ctypes.link_fundef, he, ha, hr, hc] at hl
            | left _ =>
              simp only [Ctypes.link_fundef, he, ha, hr, hc] at hl
              cases Option.some.inj hl
              exact ⟨.External ef1 args1 res1 cc1,
                by simp only [Ctypes.link_fundef, he, ha, hr, hc],
                Or.inl (tr_fundef.tr_external _ _ _ _)⟩

private theorem pg3898_list_map {A B : Type} (R S : A → B → Prop)
    (h : ∀ a b, R a b → S a b) {xs : List A} {ys : List B}
    (hl : list_forall2 R xs ys) : list_forall2 S xs ys := by
  induction hl with
  | nil => exact .nil S
  | cons a b hab htail ih => exact .cons a b (h a b hab) ih

private theorem pg3898_match_iff
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cert : Ctypes.Linker_program_obligations) (p : cprogram) (tp : tprogram) :
    match_prog p tp ↔
      (@match_program_gen cprogram cfundef ctype tfundef ctype
        (Ctypes.Linker_program cfunction cert) tr_fundef Eq p
        (Ctypes.program_of_program p) (Ctypes.program_of_program tp)) ∧
      tp.prog_types = p.prog_types := by
  letI : Linker cprogram := Ctypes.Linker_program cfunction cert
  have hg : ∀ (g : globdef cfundef ctype) (tg : globdef tfundef ctype),
      (match g, tg with
      | .Gfun f, .Gfun tf => ∃ cu, Ctypes.linkorder_program cu p ∧ tr_fundef cu f tf
      | .Gvar v, .Gvar tv => v.gvar_info = tv.gvar_info ∧ v.gvar_init = tv.gvar_init ∧
          v.gvar_readonly = tv.gvar_readonly ∧ v.gvar_volatile = tv.gvar_volatile
      | _, _ => False) ↔ match_globdef tr_fundef Eq p g tg := by
    intro g tg
    constructor
    · intro h
      cases g with
      | Gfun f =>
        cases tg with
        | Gfun tf =>
          obtain ⟨cu, hcu, hr⟩ := h
          exact match_globdef_fun tr_fundef Eq p cu f tf hcu hr
        | Gvar tv => exact h.elim
      | Gvar v =>
        cases tg with
        | Gfun tf => exact h.elim
        | Gvar tv =>
          obtain ⟨hi, hn, hr, hv⟩ := h
          cases v; cases tv
          simp only at hi hn hr hv
          subst_vars
          exact match_globdef_var tr_fundef Eq p _ _
            (match_globvar_intro Eq _ _ _ _ _ rfl)
    · intro h
      cases h with
      | match_globdef_fun cu f tf hc hr => exact ⟨cu, hc, hr⟩
      | match_globdef_var v tv hv =>
        cases pg3898_globvar_eq hv
        exact ⟨rfl, rfl, rfl, rfl⟩
  constructor
  · rintro ⟨⟨hl, hm, hp⟩, ht⟩
    refine ⟨⟨?_, hm, hp⟩, ht⟩
    exact pg3898_list_map _ _ (fun _ _ hab => ⟨hab.1, (hg _ _).mp hab.2⟩) hl
  · rintro ⟨⟨hl, hm, hp⟩, ht⟩
    refine ⟨⟨?_, hm, hp⟩, ht⟩
    exact pg3898_list_map _ _ (fun _ _ hab => ⟨hab.1, (hg _ _).mpr hab.2⟩) hl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.SimplExprspec

theorem TransfSimplExprLink :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
      (csyntaxLinkerCertificate clightLinkerCertificate : Ctypes.Linker_program_obligations),
      TransfSimplExprLinkStatement csyntaxLinkerCertificate clightLinkerCertificate := by
  intro binary64_certificate binary32_certificate cs ct
  letI : Linker cprogram := Ctypes.Linker_program cfunction cs
  letI : Linker tprogram := Ctypes.Linker_program tfunction ct
  unfold TransfSimplExprLinkStatement
  refine { transf_link := ?_ }
  intro p1 p2 tp1 tp2 p hl h1 h2
  change Ctypes.link_program cs.composite_defs p1 p2 = some p at hl
  have ho := cs.link_linkorder p1 p2 p hl
  obtain ⟨hm1, ht1⟩ := (pg3898_match_iff cs p1 tp1).mp h1
  obtain ⟨hm2, ht2⟩ := (pg3898_match_iff cs p2 tp2).mp h2
  unfold Ctypes.link_program at hl
  cases hb : link (Ctypes.program_of_program p1) (Ctypes.program_of_program p2) with
  | none => simp only [hb] at hl; cases hl
  | some pp =>
    obtain ⟨tpp, htb, hmp⟩ := @pg3898_link_ast cprogram cfundef tfundef ctype
      (Ctypes.Linker_program cfunction cs) (Ctypes.Linker_fundef cfunction)
      (Ctypes.Linker_fundef tfunction) Ctypes.Linker_types tr_fundef pg3898_link_fundef
      p1 p2 p (Ctypes.program_of_program p1) (Ctypes.program_of_program p2)
      (Ctypes.program_of_program tp1) (Ctypes.program_of_program tp2) pp
      hb hm1 hm2 ho.1 ho.2
    change link (Ctypes.program_of_program tp1) (Ctypes.program_of_program tp2) = some tpp at htb
    cases hty : Ctypes.lift_option (Ctypes.link_composite_defs p1.prog_types p2.prog_types) with
    | inright hn => simp only [hb, hty] at hl; cases hl
    | inleft types =>
      simp only [hb, hty] at hl
      cases Option.some.inj hl
      change ∃ tp, Ctypes.link_program ct.composite_defs tp1 tp2 = some tp ∧ match_prog _ tp
      unfold Ctypes.link_program
      rw [htb]
      have htyt : Ctypes.link_composite_defs tp1.prog_types tp2.prog_types = some types.val := by
        rw [ht1, ht2]
        exact types.property
      cases hty' : Ctypes.lift_option (Ctypes.link_composite_defs tp1.prog_types tp2.prog_types) with
      | inright hn => rw [htyt] at hn; cases hn
      | inleft ttypes =>
        have htypes : ttypes.val = types.val := Option.some.inj (ttypes.property.symm.trans htyt)
        refine ⟨_, rfl, ?_⟩
        apply (pg3898_match_iff cs _ _).mpr
        exact ⟨hmp, htypes⟩

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem type_of_fundef_preserved :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      type_of_fundef_preservedStatement := by
  intro binary64_certificate binary32_certificate
  intro cu f tf h
  cases h with
  | tr_internal f tf htr =>
      cases htr with
      | tr_function_intro hbody hreturn hcallconv hparams hvars =>
          simp [Clight.type_of_fundef, Csyntax.type_of_fundef,
            Clight.type_of_function, Csyntax.type_of_function,
            hreturn, hcallconv, hparams]
  | tr_external ef targs tres cconv =>
      rfl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Lib.Integers

private theorem pg4057_shift_bound (width : Z)
    (hpos : ZArith.BinInt.Z.lt .Z0 width)
    (hle : ZArith.BinInt.Z.le width Int.zwordsize) :
    Int.ltu (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub Int.zwordsize width))
      Int.iwordsize = true := by
  have hval : intOfZ (ZArith.BinInt.Z.sub Int.zwordsize width) =
      32 - intOfZ width := by
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    rfl
  have hrange :
      ZArith.BinInt.Z.le .Z0 (ZArith.BinInt.Z.sub Int.zwordsize width) ∧
      ZArith.BinInt.Z.le (ZArith.BinInt.Z.sub Int.zwordsize width)
        Int.max_unsigned := by
    change 0 < intOfZ width at hpos
    change intOfZ width ≤ 32 at hle
    change 0 ≤ intOfZ (ZArith.BinInt.Z.sub Int.zwordsize width) ∧
      intOfZ (ZArith.BinInt.Z.sub Int.zwordsize width) ≤ 4294967295
    rw [hval]
    omega
  have hlt : ZArith.BinInt.Z.lt
      (Int.unsigned (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub Int.zwordsize width)))
      (Int.unsigned Int.iwordsize) := by
    rw [Int.unsigned_repr_proof_api _ hrange, Int.unsigned_repr_wordsize_proof]
    change intOfZ (ZArith.BinInt.Z.sub Int.zwordsize width) < 32
    rw [hval]
    change 0 < intOfZ width at hpos
    omega
  exact CompCert4Lean.Lib.Coqlib.zlt_true Bool _ _ true false hlt

theorem eval_make_normalize :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_make_normalizeStatement := by
  intro binary64_certificate binary32_certificate
  intro ge e le m a n sz sg sg1 attr width hpos hwidth hty heval
  have hle : ZArith.BinInt.Z.le width Int.zwordsize := by
    change intOfZ width ≤ 32
    have hb : intOfZ (bitsize_intsize sz) ≤ 32 := by
      cases sz <;> decide
    exact _root_.Int.le_trans hwidth hb
  have hnneg : ZArith.BinInt.Z.le .Z0 width := by
    change 0 ≤ intOfZ width
    change 0 < intOfZ width at hpos
    omega
  have hzero : Clight.eval_expr ge e le m
      (.Ebinop .Oand a
        (.Econst_int (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub (two_p width) (.Zpos .xH)))
          type_int32s) (Clight.typeof a)) (.Vint (Int.zero_ext width n)) := by
    rw [Int.zero_ext_and_proof width n hnneg]
    apply Clight.eval_expr.binary
    · exact heval
    · exact Clight.eval_expr.const_int _ _
    · rw [hty]
      cases sz <;> cases sg1 <;> rfl
  have hsigned : Clight.eval_expr ge e le m
      (.Ebinop .Oshr
        (.Ebinop .Oshl a
          (.Econst_int (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub Int.zwordsize width))
            type_int32s) type_int32s)
        (.Econst_int (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub Int.zwordsize width))
          type_int32s) (Clight.typeof a)) (.Vint (Int.sign_ext width n)) := by
    rw [Int.sign_ext_shr_shl_proof width n ⟨hpos, hle⟩]
    have hlt := pg4057_shift_bound width hpos hle
    apply Clight.eval_expr.binary (v1 := .Vint (Int.shl n
      (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub Int.zwordsize width))))
    · apply Clight.eval_expr.binary
      · exact heval
      · exact Clight.eval_expr.const_int _ _
      · rw [hty]
        cases sz <;> cases sg1 <;>
          simp only [sem_binary_operation, sem_shl, sem_shift, classify_shift,
            typeconv, remove_attributes, change_attributes, type_int32s, Clight.typeof,
            hlt, if_true]
    · exact Clight.eval_expr.const_int _ _
    · simp only [sem_binary_operation, sem_shr, sem_shift, classify_shift,
        typeconv, remove_attributes, change_attributes, type_int32s, Clight.typeof,
            hlt, if_true]
  cases sz <;> cases sg <;>
    first | exact hzero | exact hsigned

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem make_assign_value_sound :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      make_assign_value_soundStatement := by
  intro binary64_certificate binary32_certificate p ty m b ofs bf v t m' v' hassign
  cases hassign with
  | value hmode hvol hstore =>
      intro tge e le m'' r hty heval
      exact heval
  | volatile hmode hvol hstore =>
      intro tge e le m'' r hty heval
      exact heval
  | copy hmode halignSource halignTarget hseparated hload hstore =>
      intro tge e le m'' r hty heval
      exact heval
  | bitfield hstore =>
      cases hstore with
      | store_bitfield_intro sz sg1 attr sg pos width m addr c n m'
          hpos hwidth hcarrier hsg hload hstore =>
          intro tge e le m'' r hty heval
          exact eval_make_normalize tge e le m'' r n _ _ sg1 attr _
            hwidth.1 hwidth.2 hty heval

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

theorem tr_simple :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_simpleStatement := by
  intro binary64_certificate binary32_certificate p tp hmatch cunit e m
  constructor
  · intro r v hEval
    exact tr_simple_rvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      p tp hmatch cunit e m r v hEval
  · intro l b ofs bf hEval
    exact tr_simple_lvalue
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      p tp hmatch cunit e m l b ofs bf hEval

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Maps

section
variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private def pg4222Decomposition (ce : composite_env) (le : ttemp_env) (e : cexpr)
    (sl : List Clight.statement) (tmps : List ident)
    (R : ttemp_env → cexpr → List Clight.statement → Prop) : Prop :=
  ∃ dst' sl1 sl2 a' tmp',
    tr_expr ce le dst' e sl1 a' tmp' ∧ sl = sl1 ++ sl2 ∧ Included tmp' tmps ∧
    ∀ le' e' sl3, tr_expr ce le' dst' e' sl3 a' tmp' →
      (∀ id, id ∉ tmp' → PTree.get id le' = PTree.get id le) →
      Csyntax.typeof e' = Csyntax.typeof e → R le' e' (sl3 ++ sl2)

private theorem pg4222Lift {ce le e sl tmps outer}
    {R S : ttemp_env → cexpr → List Clight.statement → Prop}
    (tail : List Clight.statement)
    (h : pg4222Decomposition ce le e sl tmps R)
    (hsub : Included tmps outer)
    (hlift : ∀ le' e' sl', R le' e' sl' →
      (∀ id, id ∉ tmps → PTree.get id le' = PTree.get id le) →
      Csyntax.typeof e' = Csyntax.typeof e → S le' e' (sl' ++ tail)) :
    pg4222Decomposition ce le e (sl ++ tail) outer S := by
  rcases h with ⟨dst, sl1, sl2, a, tmp, htr, rfl, hinc, hrec⟩
  refine ⟨dst, sl1, sl2 ++ tail, a, tmp, htr, List.append_assoc ..,
    fun id hid => hsub id (hinc id hid), ?_⟩
  intro le' e' sl3 htr' hagree hty
  rw [← List.append_assoc]
  apply hlift le' e' (sl3 ++ sl2) (hrec le' e' sl3 htr' hagree hty)
  · intro id hnot
    exact hagree id (fun hin => hnot (hinc id hin))
  · exact hty

private theorem pg4222LiftZero {ce le e sl tmps outer}
    {R S : ttemp_env → cexpr → List Clight.statement → Prop}
    (h : pg4222Decomposition ce le e sl tmps R)
    (hsub : Included tmps outer)
    (hlift : ∀ le' e' sl', R le' e' sl' →
      (∀ id, id ∉ tmps → PTree.get id le' = PTree.get id le) →
      Csyntax.typeof e' = Csyntax.typeof e → S le' e' sl') :
    pg4222Decomposition ce le e sl outer S := by
  simpa only [List.append_nil] using pg4222Lift [] h hsub
    (fun le' e' sl' hr ha ht => by simpa only [List.append_nil] using hlift le' e' sl' hr ha ht)

private theorem pg4222AgreeRight {xs ys : List ident} {le le' : ttemp_env}
    (hd : CompCert4Lean.Lib.Coqlib.list_disjoint xs ys)
    (ha : ∀ id, id ∉ xs → PTree.get id le' = PTree.get id le) :
    ∀ id, id ∈ ys → PTree.get id le' = PTree.get id le := by
  intro id hin
  exact ha id (fun hx => hd id id hx hin rfl)

private theorem pg4222AgreeLeft {xs ys : List ident} {le le' : ttemp_env}
    (hd : CompCert4Lean.Lib.Coqlib.list_disjoint xs ys)
    (ha : ∀ id, id ∉ ys → PTree.get id le' = PTree.get id le) :
    ∀ id, id ∈ xs → PTree.get id le' = PTree.get id le := by
  intro id hin
  exact ha id (fun hy => hd id id hin hy rfl)

private def pg4222ExprContext (cunit : cprogram) (C : cexpr → cexpr) : Prop :=
  ∀ le e dst sl a tmps, tr_expr cunit.prog_comp_env le dst (C e) sl a tmps →
    pg4222Decomposition cunit.prog_comp_env le e sl tmps
      (fun le' e' sl' => tr_expr cunit.prog_comp_env le' dst (C e') sl' a tmps)

private def pg4222ListContext (cunit : cprogram) (C : cexpr → cexprlist) : Prop :=
  ∀ le e sl a tmps, tr_exprlist cunit.prog_comp_env le (C e) sl a tmps →
    pg4222Decomposition cunit.prog_comp_env le e sl tmps
      (fun le' e' sl' => tr_exprlist cunit.prog_comp_env le' (C e') sl' a tmps)

private theorem pg4222Expr (cunit : cprogram) {kfrom kto C}
    (hctx : leftcontext kfrom kto C) : pg4222ExprContext cunit C := by
  induction hctx using leftcontext.rec
    (motive_2 := fun C _ => pg4222ListContext cunit C) with
  | lctx_top =>
    intro le e dst sl a tmps htr
    refine ⟨dst, sl, [], a, tmps, htr, (List.append_nil _).symm,
      fun _ h => h, ?_⟩
    intro le' e' sl3 htr' _ _
    simpa only [List.append_nil] using htr'
  | lctx_deref hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_deref _ _ ty sl1 a1 _ h1 =>
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      exact tr_expr.tr_deref _ _ _ _ _ _ _ hinner
  | lctx_field hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_field _ _ f ty sl1 a1 _ h1 =>
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      exact tr_expr.tr_field _ _ _ _ _ _ _ _ hinner
  | lctx_rvalof hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_valof _ _ ty _ sl1 a1 tmp1 sl2 a2 tmp2 h1 h2 hd hi1 hi2 =>
      simp only [List.append_assoc]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hi1
      intro le' e' sl' hinner hagree htype
      simp only [← List.append_assoc]
      apply tr_expr.tr_valof _ _ _ _ _ _ _ _ _ _ _ hinner
      · simpa only [typeof_context _ _ _ hctx _ _ htype] using h2
      · exact hd
      · exact hi1
      · exact hi2
  | lctx_addrof hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_addrof _ _ ty _ sl1 a1 h1 =>
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      exact tr_expr.tr_addrof _ _ _ _ _ _ _ hinner
  | lctx_unop hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_unop _ op _ ty _ sl1 a1 h1 =>
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      exact tr_expr.tr_unop _ _ _ _ _ _ _ _ hinner
  | lctx_binop_left hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_binop dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2)
  | lctx_binop_right hs hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_binop dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_binop _ _ _ _ _ _ _ _ _ _ _ _ _ h1' hinner hdisjoint hincl1 hincl2)
  | lctx_cast hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_cast_effects e1 ty sl1 a1 any tmp h1 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222LiftZero (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_cast_effects _ _ _ _ _ _ _ hinner)
    | tr_cast_val dst e1 ty sl1 a1 tmp h1 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_cast_val _ _ _ _ _ _ _ hinner)
  | lctx_seqand hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_seqand_val e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_seqand_val _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2 htmp)
    | tr_seqand_effects e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp h1 h2 hdisjoint hincl1 hincl2 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_seqand_effects _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2)
    | tr_seqand_set sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp h1 h2 hdisjoint hincl1 hincl2 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_seqand_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2 htmp)
  | lctx_seqor hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_seqor_val e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_seqor_val _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2 htmp)
    | tr_seqor_effects e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp h1 h2 hdisjoint hincl1 hincl2 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_seqor_effects _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2)
    | tr_seqor_set sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp h1 h2 hdisjoint hincl1 hincl2 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_seqor_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2 htmp)
  | lctx_condition hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_condition_val e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp h1 h2 h3 hdisjoint12 hdisjoint13 hincl1 hincl2 hincl3 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint12 hagree)
      have h3' := tr_expr_invariant _ _ _ _ _ _ _ h3 le' (pg4222AgreeRight hdisjoint13 hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_condition_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' h3' hdisjoint12 hdisjoint13 hincl1 hincl2 hincl3 htmp)
    | tr_condition_effects e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp h1 h2 h3 hdisjoint12 hdisjoint13 hincl1 hincl2 hincl3 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint12 hagree)
      have h3' := tr_expr_invariant _ _ _ _ _ _ _ h3 le' (pg4222AgreeRight hdisjoint13 hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_condition_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' h3' hdisjoint12 hdisjoint13 hincl1 hincl2 hincl3)
    | tr_condition_set sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp h1 h2 h3 hdisjoint12 hdisjoint13 hincl1 hincl2 hincl3 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint12 hagree)
      have h3' := tr_expr_invariant _ _ _ _ _ _ _ h3 le' (pg4222AgreeRight hdisjoint13 hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_condition_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' h3' hdisjoint12 hdisjoint13 hincl1 hincl2 hincl3 htmp)
  | lctx_assign_left hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_assign_effects e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp h1 h2 hdisjoint hincl1 hincl2 haccess =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2 haccess)
    | tr_assign_val dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2 bf h1 h2 hincl1 hincl2 hdisjoint htmp hnot1 hnot2 hty1 hty2 haccess =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      have hty1' : _ := hty1.trans hctype.symm
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hincl1 hincl2 hdisjoint htmp hnot1 hnot2 hty1' hty2 haccess)
  | lctx_assign_right hs hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_assign_effects e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp h1 h2 hdisjoint hincl1 hincl2 haccess =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assign_effects _ _ _ _ _ _ _ _ _ _ _ _ _ h1' hinner hdisjoint hincl1 hincl2 haccess)
    | tr_assign_val dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2 bf h1 h2 hincl1 hincl2 hdisjoint htmp hnot1 hnot2 hty1 hty2 haccess =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint hagree)
      have hty2' : _ := hty2.trans hctype.symm
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assign_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1' hinner hincl1 hincl2 hdisjoint htmp hnot1 hnot2 hty1 hty2' haccess)
  | lctx_assignop_left hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_assignop_effects op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3 any tmp h1 h2 hty1 h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 haccess =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint12 hagree)
      have hty1' : _ := hty1.trans hctype.symm
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hty1' h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 haccess)
    | tr_assignop_val dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf tmp ty1 h1 h2 h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 htmp hnot1 hnot2 hnot3 hty1 haccess =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint12 hagree)
      have hty1' : _ := hty1.trans hctype.symm
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 htmp hnot1 hnot2 hnot3 hty1' haccess)
  | lctx_assignop_right hs hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_assignop_effects op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3 any tmp h1 h2 hty1 h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 haccess =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint12 hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assignop_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1' hinner hty1 h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 haccess)
    | tr_assignop_val dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf tmp ty1 h1 h2 h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 htmp hnot1 hnot2 hnot3 hty1 haccess =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint12 hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_assignop_val _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1' hinner h3 hdisjoint12 hdisjoint13 hdisjoint23 hincl1 hincl2 hincl3 htmp hnot1 hnot2 hnot3 hty1 haccess)
  | lctx_postincr hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_postincr_effects id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp h1 h2 hty1 hincl1 hincl2 hdisjoint haccess =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have hty1' : _ := hty1.trans hctype.symm
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_postincr_effects _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinner h2 hty1' hincl1 hincl2 hdisjoint haccess)
    | tr_postincr_val dst id e1 ty sl1 a1 tmp1 bf t ty1 tmp h1 hincl1 htmp hnot1 hty1 haccess =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have hty1' : _ := hty1.trans hctype.symm
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_postincr_val _ _ _ _ _ _ _ _ _ _ _ _ hinner hincl1 htmp hnot1 hty1' haccess)
  | lctx_call_left hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_call_effects e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp h1 h2 hdisjoint hincl1 hincl2 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_exprlist_invariant _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2)
    | tr_call_val dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp hdst h1 h2 hdisjoint htmp hincl1 hincl2 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_exprlist_invariant _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ hdst hinner h2' hdisjoint htmp hincl1 hincl2)
  | lctx_call_right hs hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_call_effects e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp h1 h2 hdisjoint hincl1 hincl2 =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_call_effects _ _ _ _ _ _ _ _ _ _ _ _ h1' hinner hdisjoint hincl1 hincl2)
    | tr_call_val dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp hdst h1 h2 hdisjoint htmp hincl1 hincl2 =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ h2) hincl2
      intro le' e' sl' hinner hagree htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_call_val _ _ _ _ _ _ _ _ _ _ _ _ _ hdst h1' hinner hdisjoint htmp hincl1 hincl2)
  | lctx_builtin hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_builtin_effects ef tyargs el ty sl al tmp1 any tmp h1 hincl =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ h1) hincl
      intro le' e' sl' hinner hagree htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_builtin_effects _ _ _ _ _ _ _ _ _ _ hinner hincl)
    | tr_builtin_val dst ef tyargs el ty sl al tmp1 t tmp hdst h1 htmp hincl =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ h1) hincl
      intro le' e' sl' hinner hagree htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_builtin_val _ _ _ _ _ _ _ _ _ _ _ hdst hinner htmp hincl)
  | lctx_comma hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_comma dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp h1 h2 hdisjoint hincl1 hincl2 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hincl1
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      have h2' := tr_expr_invariant _ _ _ _ _ _ _ h2 le' (pg4222AgreeRight hdisjoint hagree)
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_comma _ _ _ _ _ _ _ _ _ _ _ _ hinner h2' hdisjoint hincl1 hincl2)
  | lctx_paren hctx ih =>
    intro le e dst sl a tmps htr
    cases htr with
    | tr_paren_val e1 tycast ty sl1 a1 t tmp h1 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222LiftZero (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_paren_val _ _ _ _ _ _ _ _ hinner htmp)
    | tr_paren_effects e1 tycast ty sl1 a1 tmp any h1 =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222LiftZero (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_paren_effects _ _ _ _ _ _ _ _ hinner)
    | tr_paren_set t sd e1 tycast ty sl1 a1 tmp any h1 htmp =>
      simp only [List.append_assoc, List.nil_append]
      apply pg4222LiftZero (ih _ _ _ _ _ _ h1) (fun _ h => h)
      intro le' e' sl' hinner hagree htype
      have hctype := typeof_context _ _ _ hctx _ _ htype
      simpa only [List.append_assoc, List.nil_append] using
        (tr_expr.tr_paren_set _ _ _ _ _ _ _ _ _ _ hinner htmp)
  | lctx_list_head hctx ih =>
    intro le e sl a tmps htr
    cases htr with
    | tr_cons _ el sl1 a1 tmp1 sl2 al2 tmp2 _ h1 h2 hd hi1 hi2 =>
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hi1
      intro le' e' sl' hinner hagree htype
      apply tr_exprlist.tr_cons _ _ _ _ _ _ _ _ _ _ hinner
      · exact tr_exprlist_invariant _ _ _ _ _ _ h2 le' (pg4222AgreeRight hd hagree)
      · exact hd
      · exact hi1
      · exact hi2
  | lctx_list_tail hs hctx ih =>
    intro le e sl a tmps htr
    cases htr with
    | tr_cons r el sl1 a1 tmp1 sl2 al2 tmp2 _ h1 h2 hd hi1 hi2 =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.nil_append]
      apply pg4222LiftZero (ih _ _ _ _ _ h2) hi2
      intro le' e' sl' hinner hagree htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hd hagree)
      simpa only [List.nil_append] using
        tr_exprlist.tr_cons le' _ _ [] _ _ sl' _ _ _ h1' hinner hd hi1 hi2

private theorem pg4222List (cunit : cprogram) {kfrom C}
    (hctx : leftcontextlist kfrom C) : pg4222ListContext cunit C := by
  induction hctx using leftcontextlist.rec
    (motive_1 := fun _ C _ => pg4222ExprContext cunit C) with
  | lctx_top => exact pg4222Expr cunit (.lctx_top kfrom)
  | lctx_deref hctx _ =>
    exact pg4222Expr cunit (.lctx_deref hctx)
  | lctx_field hctx _ =>
    exact pg4222Expr cunit (.lctx_field hctx)
  | lctx_rvalof hctx _ =>
    exact pg4222Expr cunit (.lctx_rvalof hctx)
  | lctx_addrof hctx _ =>
    exact pg4222Expr cunit (.lctx_addrof hctx)
  | lctx_unop hctx _ =>
    exact pg4222Expr cunit (.lctx_unop hctx)
  | lctx_binop_left hctx _ =>
    exact pg4222Expr cunit (.lctx_binop_left hctx)
  | lctx_binop_right hs hctx _ =>
    exact pg4222Expr cunit (.lctx_binop_right hs hctx)
  | lctx_cast hctx _ =>
    exact pg4222Expr cunit (.lctx_cast hctx)
  | lctx_seqand hctx _ =>
    exact pg4222Expr cunit (.lctx_seqand hctx)
  | lctx_seqor hctx _ =>
    exact pg4222Expr cunit (.lctx_seqor hctx)
  | lctx_condition hctx _ =>
    exact pg4222Expr cunit (.lctx_condition hctx)
  | lctx_assign_left hctx _ =>
    exact pg4222Expr cunit (.lctx_assign_left hctx)
  | lctx_assign_right hs hctx _ =>
    exact pg4222Expr cunit (.lctx_assign_right hs hctx)
  | lctx_assignop_left hctx _ =>
    exact pg4222Expr cunit (.lctx_assignop_left hctx)
  | lctx_assignop_right hs hctx _ =>
    exact pg4222Expr cunit (.lctx_assignop_right hs hctx)
  | lctx_postincr hctx _ =>
    exact pg4222Expr cunit (.lctx_postincr hctx)
  | lctx_call_left hctx _ =>
    exact pg4222Expr cunit (.lctx_call_left hctx)
  | lctx_call_right hs hctx _ =>
    exact pg4222Expr cunit (.lctx_call_right hs hctx)
  | lctx_builtin hctx _ =>
    exact pg4222Expr cunit (.lctx_builtin hctx)
  | lctx_comma hctx _ =>
    exact pg4222Expr cunit (.lctx_comma hctx)
  | lctx_paren hctx _ =>
    exact pg4222Expr cunit (.lctx_paren hctx)
  | lctx_list_head hctx ih =>
    intro le e sl a tmps htr
    cases htr with
    | tr_cons _ el sl1 a1 tmp1 sl2 al2 tmp2 _ h1 h2 hd hi1 hi2 =>
      apply pg4222Lift _ (ih _ _ _ _ _ _ h1) hi1
      intro le' e' sl' hinner hagree htype
      apply tr_exprlist.tr_cons _ _ _ _ _ _ _ _ _ _ hinner
      · exact tr_exprlist_invariant _ _ _ _ _ _ h2 le' (pg4222AgreeRight hd hagree)
      · exact hd
      · exact hi1
      · exact hi2
  | lctx_list_tail hs hctx ih =>
    intro le e sl a tmps htr
    cases htr with
    | tr_cons r el sl1 a1 tmp1 sl2 al2 tmp2 _ h1 h2 hd hi1 hi2 =>
      have hn := tr_simple_expr_nil cunit _ _ _ _ _ _ h1 (Or.inl rfl) hs
      subst sl1
      simp only [List.nil_append]
      apply pg4222LiftZero (ih _ _ _ _ _ h2) hi2
      intro le' e' sl' hinner hagree htype
      have h1' := tr_expr_invariant _ _ _ _ _ _ _ h1 le' (pg4222AgreeLeft hd hagree)
      simpa only [List.nil_append] using
        tr_exprlist.tr_cons le' _ _ [] _ _ sl' _ _ _ h1' hinner hd hi1 hi2

theorem tr_expr_leftcontext_rec : tr_expr_leftcontext_recStatement := by
  intro cunit
  constructor
  · intro kfrom kto C hctx
    exact pg4222Expr cunit hctx
  · intro kfrom C hctx
    exact pg4222List cunit hctx

end
end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem tr_expr_leftcontext :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_expr_leftcontextStatement := by
  intro binary64_certificate binary32_certificate
  intro cunit C le r dst sl a tmps hctx htr
  have hrec := tr_expr_leftcontext_rec
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    cunit
  exact hrec.1 .RV .RV C hctx le r dst sl a tmps htr

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec

 theorem tr_top_leftcontext :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      tr_top_leftcontextStatement := by
  intro binary64_certificate binary32_certificate
  intro tprog cunit e le m dst rtop sl a tmps htop
  intro r C hrtop hctx
  cases htop with
  | tr_top_val_val v ty a tmps htype heval =>
      cases hctx <;> simp_all [Function.comp_def] <;> subst_vars
      refine ⟨.For_val, [], [], a, tmps, ?_⟩
      refine ⟨?_, ?_⟩
      · exact CompCert4Lean.Cfrontend.SimplExprspec.tr_top_val_val
          (ce := cunit.prog_comp_env) v (Clight.typeof a) a tmps rfl heval
      refine ⟨⟨rfl, rfl⟩, ?_⟩
      refine ⟨CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl_refl _, ?_⟩
      intro le' m' r' sl3 htr hincl htype'
      simpa only [List.append_nil] using
        (CompCert4Lean.Cfrontend.SimplExprspec.tr_top_base
          (ce := cunit.prog_comp_env) (ge := Clight.globalenv tprog)
          (e := e) (le := le') (m := m') .For_val r' sl3 a tmps htr)
  | tr_top_base _ _ _ _ _ htr =>
      rw [hrtop] at htr
      have h := tr_expr_leftcontext
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        cunit C le r dst sl a tmps hctx htr
      rcases h with ⟨dst', sl1, sl2, a', tmp', htr', hsl, hincl, hrec⟩
      refine ⟨dst', sl1, sl2, a', tmp', ?_, hsl, hincl, ?_⟩
      · exact CompCert4Lean.Cfrontend.SimplExprspec.tr_top_base
          (ce := cunit.prog_comp_env) dst' r sl1 a' tmp' htr'
      · intro le' m' r' sl3 htr'' hincl' htype'
        exact CompCert4Lean.Cfrontend.SimplExprspec.tr_top_base
          (ce := cunit.prog_comp_env) dst (C r') (sl3 ++ sl2) a tmps
          (hrec le' r' sl3 htr'' hincl' htype')

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Memory

 theorem step_makeif :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      step_makeifStatement := by
  intro binary64_certificate binary32_certificate
  intro xi tp f a s1 s2 k e le m v1 b heval hbool
  unfold makeif
  cases hev : eval_simpl_expr a with
  | none =>
      apply star_one
      exact Clight.step_ifthenelse f a s1 s2 k e le m v1 b heval hbool
  | some v =>
      have hv : v = v1 := by
        simpa [hev] using
          (eval_simpl_expr_sound
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            tp e le m a v1 heval)
      subst v
      cases hb : bool_val v1 (Clight.typeof a)
          CompCert4Lean.Common.Memory.Mem.empty with
      | none =>
          simp only [hev, hb]
          apply star_one
          exact Clight.step_ifthenelse f a s1 s2 k e le m v1 b heval hbool
      | some b' =>
          have hstatic := static_bool_val_sound v1 (Clight.typeof a) m b' hb
          have hbeq : b' = b := Option.some.inj (hstatic.symm.trans hbool)
          subst b'
          cases b with
          | false =>
              simpa [hev, hb] using
                (star_refl (Clight.step1 xi) (Clight.globalenv tp)
                  (Clight.State f s2 k e le m))
          | true =>
              simpa [hev, hb] using
                (star_refl (Clight.step1 xi) (Clight.globalenv tp)
                  (Clight.State f s1 k e le m))

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Events
open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Cfrontend.Cstrategy
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Maps

section
variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

private def pg4376Local (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (e : cenv) (m : mem) (r : cexpr) (t : trace) (m' : mem) (r' : cexpr) : Prop :=
  ∀ (cu : cprogram), Ctypes.linkorder_program cu p →
  ∀ le dst sl a tmp, tr_expr cu.prog_comp_env le dst r sl a tmp →
  ∀ tf tk, ∃ le' sl',
    (plus (Clight.step1 xi) (Clight.globalenv tp)
      (.State tf .Sskip (Kseqlist sl tk) e le m) t
      (.State tf .Sskip (Kseqlist sl' tk) e le' m') ∨
    (star (Clight.step1 xi) (Clight.globalenv tp)
      (.State tf .Sskip (Kseqlist sl tk) e le m) t
      (.State tf .Sskip (Kseqlist sl' tk) e le' m') ∧ esize r' < esize r)) ∧
    tr_expr cu.prog_comp_env le' dst r' sl' a tmp ∧
    (∀ id, id ∉ tmp → PTree.get id le' = PTree.get id le)

private theorem pg4376_lift (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (e : cenv) (m : mem) (r : cexpr) (t : trace) (m' : mem) (r' : cexpr)
    (hnot : ∀ v ty, r ≠ .Eval v ty)
    (htype : Csyntax.typeof r' = Csyntax.typeof r)
    (hlocal : pg4376Local xi p tp e m r t m' r')
    (f : cfunction) (k : ccont) (C : cexpr → cexpr)
    (hc : leftcontext .RV .RV C) (s : tstate)
    (hs : match_states p tp (.ExprState f (C r) k e m) s) :
    ∃ s', (plus (Clight.step1 xi) (Clight.globalenv tp) s t s' ∨
      (star (Clight.step1 xi) (Clight.globalenv tp) s t s' ∧
       measure (.ExprState f (C r') k e m') < measure (.ExprState f (C r) k e m))) ∧
      match_states p tp (.ExprState f (C r') k e m') s' := by
  cases hs with
  | match_exprstates _ _ _ _ _ tf sl tk le dst a tmp cu hlink htf htr hmk =>
    obtain ⟨dst1, sl1, sl2, a1, tmp1, htr1, hsl, hinc, hrec⟩ :=
      tr_top_leftcontext tp cu e le m dst (C r) sl a tmp htr r C rfl hc
    have hr : tr_expr cu.prog_comp_env le dst1 r sl1 a1 tmp1 := by
      cases htr1 with
      | tr_top_val_val v ty _ _ _ _ => exact False.elim (hnot v ty rfl)
      | tr_top_base _ _ _ _ _ h => exact h
    obtain ⟨le', sl', hex, hr', hagree⟩ :=
      hlocal cu hlink le dst1 sl1 a1 tmp1 hr tf (Kseqlist sl2 tk)
    subst sl
    refine ⟨.State tf .Sskip (Kseqlist (sl' ++ sl2) tk) e le' m', ?_,
      match_exprstates f (C r') k e m' tf (sl' ++ sl2) tk le' dst a tmp cu
        hlink htf (hrec le' m' r' sl' hr' hagree htype) hmk⟩
    rw [Kseqlist_app sl1 sl2 tk, Kseqlist_app sl' sl2 tk]
    rcases hex with hp | ⟨hst, hsize⟩
    · exact Or.inl hp
    · exact Or.inr ⟨hst, Nat.add_lt_add_right (leftcontext_size _ _ _ hc _ _ hsize) 1⟩

private theorem pg4376_expr (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (f : cfunction) (r : cexpr) (k : ccont)
    (e : cenv) (m : mem) (v : val)
    (heval : eval_simple_rvalue (Csem.globalenv p) e m r v)
    (hnot : match r with | .Eval _ _ => False | _ => True)
    (s : tstate) (hs : match_states p tp (.ExprState f r k e m) s) :
    ∃ s', (plus (Clight.step1 xi) (Clight.globalenv tp) s E0 s' ∨
      (star (Clight.step1 xi) (Clight.globalenv tp) s E0 s' ∧
       measure (.ExprState f (.Eval v (Csyntax.typeof r)) k e m) <
         measure (.ExprState f r k e m))) ∧
      match_states p tp (.ExprState f (.Eval v (Csyntax.typeof r)) k e m) s' := by
  cases hs with
  | match_exprstates _ _ _ _ _ tf sl tk le dst a tmp cu hlink htf htr hmk =>
    have hr : tr_expr cu.prog_comp_env le dst r sl a tmp := by
      cases htr with
      | tr_top_val_val => contradiction
      | tr_top_base _ _ _ _ _ h => exact h
    have hv := tr_simple_rvalue p tp hp cu e m r v heval le dst sl a tmp hr
    have hsize : esize r > 0 := by cases r <;> simp_all [esize]
    cases dst with
    | For_val =>
      obtain ⟨rfl, hty, hev⟩ := hv
      refine ⟨_, Or.inr ⟨star_refl _ _ _, ?_⟩,
        match_exprstates _ _ _ _ _ tf [] tk le .For_val a tmp cu hlink htf ?_ hmk⟩
      · simpa only [measure, esize] using Nat.add_lt_add_right hsize 1
      · exact tr_top.tr_top_val_val v _ a tmp hty.symm hev
    | For_effects =>
      subst sl
      refine ⟨_, Or.inr ⟨star_refl _ _ _, ?_⟩,
        match_exprstates _ _ _ _ _ tf [] tk le .For_effects a tmp cu hlink htf ?_ hmk⟩
      · simpa only [measure, esize] using Nat.add_lt_add_right hsize 1
      · exact tr_top.tr_top_base _ _ _ _ _ (tr_expr.tr_val_effect _ _ _ _ _)
    | For_set sd => cases hmk

private theorem pg4376_comma (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r1 r2 : cexpr) (ty : ctype)
    (v : val) (heval : eval_simple_rvalue (Csem.globalenv p) e m r1 v) :
    pg4376Local xi p tp e m (.Ecomma r1 r2 ty) E0 m r2 := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_comma _ _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 tmp h1 h2 hd hi1 hi2 =>
    have hnil := tr_simple_rvalue p tp hp cu e m r1 v heval le .For_effects sl1 a1 tmp1 h1
    subst sl1
    refine ⟨le, sl2, Or.inr ⟨star_refl _ _ _, ?_⟩, ?_, fun _ _ => rfl⟩
    · simp only [esize]; omega
    · exact tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2

private theorem pg4376_set_agree (le : ttemp_env) (tmp : List ident)
    (id : ident) (v : val) (hin : id ∈ tmp) :
    ∀ x, x ∉ tmp → PTree.get x (PTree.set id v le) = PTree.get x le := by
  intro x hx
  apply PTree.gso
  intro heq
  exact hx (heq ▸ hin)

private theorem pg4376_temp_eval (le : ttemp_env) (tmp : List ident)
    (id : ident) (v : val) (ty : ctype) (hin : id ∈ tmp) :
    ∀ tge e le' m, (∀ x, x ∈ tmp → PTree.get x le' = PTree.get x (PTree.set id v le)) →
    Clight.eval_expr tge e le' m (.Etempvar id ty) v := by
  intro tge e le' m hagree
  exact Clight.eval_expr.eval_Etempvar id ty v ((hagree id hin).trans (PTree.gss id v le))

private theorem pg4376_paren (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r : cexpr) (tycast ty : ctype)
    (v1 v : val) (heval : eval_simple_rvalue (Csem.globalenv p) e m r v1)
    (hcast : sem_cast v1 (Csyntax.typeof r) tycast m = some v) :
    pg4376Local xi p tp e m (.Eparen r tycast ty) E0 m (.Eval v ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_paren_val _ _ _ sl a1 id tmp h1 hin =>
    obtain ⟨b, hsl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r v1 heval
      le (.For_set (.SDbase tycast ty id)) sl a1 tmp h1
    subst sl
    refine ⟨PTree.set id v le, [], Or.inl ?_, ?_, pg4376_set_agree le tmp id v hin⟩
    · apply plus_two
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · apply Clight.step_set
        exact Clight.eval_expr.cast _ _ _ _ hev (hty ▸ hcast)
      · rfl
    · exact tr_expr.tr_val_value _ _ _ _ _ rfl (pg4376_temp_eval le tmp id v ty hin)
  | tr_paren_effects _ _ _ sl a1 tmp any h1 =>
    have hnil := tr_simple_rvalue p tp hp cu e m r v1 heval le .For_effects sl a1 tmp h1
    subst sl
    refine ⟨le, [], Or.inr ⟨star_refl _ _ _, ?_⟩,
      tr_expr.tr_val_effect _ _ _ _ _, fun _ _ => rfl⟩
    simp only [esize]; omega
  | tr_paren_set id sd _ _ _ sl a1 tmp any h1 hin =>
    obtain ⟨b, hsl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r v1 heval
      le (.For_set (.SDcons tycast ty id sd)) sl a1 tmp h1
    subst sl
    refine ⟨PTree.set id v le, do_set sd (.Etempvar id ty), Or.inl ?_, ?_,
      pg4376_set_agree le tmp id v hin⟩
    · apply plus_two
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · apply Clight.step_set
        exact Clight.eval_expr.cast _ _ _ _ hev (hty ▸ hcast)
      · rfl
    · exact tr_expr.tr_val_set _ _ _ _ _ _ _ rfl (pg4376_temp_eval le tmp id v ty hin)

private theorem pg4376_if {xi : ExternalCalls} {tp : tprogram}
    {tf : tfunction} {a : Clight.expr} {s1 s2 : Clight.statement} {tk : tcont}
    {e : cenv} {le le' : ttemp_env} {m m' : mem} {v : val} {b : Bool}
    {sl : List Clight.statement}
    (hev : Clight.eval_expr (Clight.globalenv tp) e le m a v)
    (hb : bool_val v (Clight.typeof a) m = some b)
    (hex : star (Clight.step1 xi) (Clight.globalenv tp)
      (.State tf (if b then s1 else s2) tk e le m) E0
      (.State tf .Sskip (Kseqlist sl tk) e le' m')) :
    plus (Clight.step1 xi) (Clight.globalenv tp)
      (.State tf .Sskip (Kseqlist [makeif a s1 s2] tk) e le m) E0
      (.State tf .Sskip (Kseqlist sl tk) e le' m') := by
  refine plus_left (s2 := .State tf (makeif a s1 s2) tk e le m) _ E0 ?_ ?_ rfl
  · exact Clight.step_skip_seq _ _ _ _ _ _
  exact star_trans _ _ _ _ _ _ _ (step_makeif xi tp tf a s1 s2 tk e le m v b hev hb)
    _ _ _ hex rfl

private theorem pg4376_seqand_continue (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r1 r2 : cexpr) (ty : ctype)
    (v : val) (heval : eval_simple_rvalue (Csem.globalenv p) e m r1 v)
    (hbool : bool_val v (Csyntax.typeof r1) m = some true) :
    pg4376Local xi p tp e m (.Eseqand r1 r2 ty) E0 m (.Eparen r2 type_bool ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_seqand_val _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
    · exact tr_expr.tr_paren_val _ _ _ _ _ _ _ _
        (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2) hin
  | tr_seqand_effects _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
    · exact tr_expr.tr_paren_effects _ _ _ _ _ _ _ _
        (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2)
  | tr_seqand_set sd _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
    · exact tr_expr.tr_paren_set _ id sd _ _ _ _ _ _ _
        (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2) hin

private theorem pg4376_seqor_continue (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r1 r2 : cexpr) (ty : ctype)
    (v : val) (heval : eval_simple_rvalue (Csem.globalenv p) e m r1 v)
    (hbool : bool_val v (Csyntax.typeof r1) m = some false) :
    pg4376Local xi p tp e m (.Eseqor r1 r2 ty) E0 m (.Eparen r2 type_bool ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_seqor_val _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
    · exact tr_expr.tr_paren_val _ _ _ _ _ _ _ _
        (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2) hin
  | tr_seqor_effects _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
    · exact tr_expr.tr_paren_effects _ _ _ _ _ _ _ _
        (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2)
  | tr_seqor_set sd _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
    · exact tr_expr.tr_paren_set _ id sd _ _ _ _ _ _ _
        (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2) hin

private theorem pg4376_seqand_stop (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r1 r2 : cexpr) (ty : ctype)
    (v : val) (heval : eval_simple_rvalue (Csem.globalenv p) e m r1 v)
    (hbool : bool_val v (Csyntax.typeof r1) m = some false) :
    pg4376Local xi p tp e m (.Eseqand r1 r2 ty) E0 m
      (.Eval (.Vint CompCert4Lean.Lib.Integers.Int.zero) ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_seqand_val _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨PTree.set id (.Vint CompCert4Lean.Lib.Integers.Int.zero) le, [],
      Or.inl ?_, ?_, pg4376_set_agree _ _ _ _ hin⟩
    · apply pg4376_if (b := false) hev (hty ▸ hbool)
      apply star_one
      exact Clight.step_set _ _ _ _ _ _ _ _ (.const_int _ _)
    · exact tr_expr.tr_val_value _ _ _ _ _ rfl (pg4376_temp_eval _ _ _ _ _ hin)
  | tr_seqand_effects _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, [], Or.inl ?_, tr_expr.tr_val_effect _ _ _ _ _, fun _ _ => rfl⟩
    exact pg4376_if (b := false) hev (hty ▸ hbool) (star_refl _ _ _)
  | tr_seqand_set sd _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, do_set sd (.Econst_int CompCert4Lean.Lib.Integers.Int.zero ty),
      Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf _ tk e le m)
    · exact tr_expr.tr_val_set _ _ _ _ _ _ _ rfl (fun _ _ _ _ _ => .const_int _ _)

private theorem pg4376_seqor_stop (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r1 r2 : cexpr) (ty : ctype)
    (v : val) (heval : eval_simple_rvalue (Csem.globalenv p) e m r1 v)
    (hbool : bool_val v (Csyntax.typeof r1) m = some true) :
    pg4376Local xi p tp e m (.Eseqor r1 r2 ty) E0 m
      (.Eval (.Vint CompCert4Lean.Lib.Integers.Int.one) ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_seqor_val _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨PTree.set id (.Vint CompCert4Lean.Lib.Integers.Int.one) le, [],
      Or.inl ?_, ?_, pg4376_set_agree _ _ _ _ hin⟩
    · apply pg4376_if (b := true) hev (hty ▸ hbool)
      apply star_one
      exact Clight.step_set _ _ _ _ _ _ _ _ (.const_int _ _)
    · exact tr_expr.tr_val_value _ _ _ _ _ rfl (pg4376_temp_eval _ _ _ _ _ hin)
  | tr_seqor_effects _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, [], Or.inl ?_, tr_expr.tr_val_effect _ _ _ _ _, fun _ _ => rfl⟩
    exact pg4376_if (b := true) hev (hty ▸ hbool) (star_refl _ _ _)
  | tr_seqor_set sd _ _ _ sl1 a1 tmp1 id sl2 a2 tmp2 any tmp h1 h2 hd hi1 hi2 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    refine ⟨le, do_set sd (.Econst_int CompCert4Lean.Lib.Integers.Int.one ty),
      Or.inl ?_, ?_, fun _ _ => rfl⟩
    · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf _ tk e le m)
    · exact tr_expr.tr_val_set _ _ _ _ _ _ _ rfl (fun _ _ _ _ _ => .const_int _ _)

private theorem pg4376_volatile (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (l : cexpr)
    (b : block) (ofs : ptrofs) (bf : bitfield) (t : trace) (v : val)
    (heval : eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf)
    (hderef : Csem.deref_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t v)
    (hvol : type_is_volatile (Csyntax.typeof l) = true) :
    pg4376Local xi p tp e m (.Evalof l (Csyntax.typeof l)) t m
      (.Eval v (Csyntax.typeof l)) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_valof dst _ _ tmp sl1 a1 tmp1 sl2 a2 tmp2 h1 h2 hd hi1 hi2 =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf heval
      le sl1 a1 tmp1 h1
    cases h2 with
    | tr_rvalof_nonvol _ hv => simp_all
    | tr_rvalof_vol id bf' _ hv hin hbf =>
      have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev hbf
      subst bf'
      have hin' := hi2 id hin
      refine ⟨PTree.set id v le, final dst (.Etempvar id (Csyntax.typeof l)),
        Or.inl ?_, ?_, pg4376_set_agree _ _ _ _ hin'⟩
      · apply plus_two
        · exact Clight.step_skip_seq _ _ _ _ _ _
        · exact step_make_set xi p tp hp id a1 _ m b ofs bf t v e le tf _ hderef hev hty.symm
        · rfl
      · exact tr_val_gen _ _ _ _ _ _ _ rfl (pg4376_temp_eval _ _ _ _ _ hin')

private theorem pg4376_condition (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (r1 r2 r3 : cexpr) (ty : ctype)
    (v : val) (b : Bool) (heval : eval_simple_rvalue (Csem.globalenv p) e m r1 v)
    (hbool : bool_val v (Csyntax.typeof r1) m = some b) :
    pg4376Local xi p tp e m (.Econdition r1 r2 r3 ty) E0 m
      (.Eparen (if b then r2 else r3) ty ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_condition_val _ _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 id tmp h1 h2 h3 hd1 hd2 hi1 hi2 hi3 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    cases b with
    | false =>
      refine ⟨le, sl3, Or.inl ?_, ?_, fun _ _ => rfl⟩
      · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf sl3 tk e le m)
      · exact tr_expr.tr_paren_val _ _ _ _ _ _ _ _
          (tr_expr_monotone _ _ _ _ _ _ _ h3 tmp hi3) hin
    | true =>
      refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
      · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
      · exact tr_expr.tr_paren_val _ _ _ _ _ _ _ _
          (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2) hin
  | tr_condition_effects _ _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp h1 h2 h3 hd1 hd2 hi1 hi2 hi3 =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    cases b with
    | false =>
      refine ⟨le, sl3, Or.inl ?_, ?_, fun _ _ => rfl⟩
      · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf sl3 tk e le m)
      · exact tr_expr.tr_paren_effects _ _ _ _ _ _ _ _
          (tr_expr_monotone _ _ _ _ _ _ _ h3 tmp hi3)
    | true =>
      refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
      · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
      · exact tr_expr.tr_paren_effects _ _ _ _ _ _ _ _
          (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2)
  | tr_condition_set sd id _ _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp h1 h2 h3 hd1 hd2 hi1 hi2 hi3 hin =>
    obtain ⟨rfl, hty, hev⟩ := tr_simple_rvalue p tp hp cu e m r1 v heval
      le .For_val sl1 a1 tmp1 h1
    cases b with
    | false =>
      refine ⟨le, sl3, Or.inl ?_, ?_, fun _ _ => rfl⟩
      · exact pg4376_if (b := false) hev (hty ▸ hbool) (push_seq xi tp tf sl3 tk e le m)
      · exact tr_expr.tr_paren_set _ id sd _ _ _ _ _ _ _
          (tr_expr_monotone _ _ _ _ _ _ _ h3 tmp hi3) hin
    | true =>
      refine ⟨le, sl2, Or.inl ?_, ?_, fun _ _ => rfl⟩
      · exact pg4376_if (b := true) hev (hty ▸ hbool) (push_seq xi tp tf sl2 tk e le m)
      · exact tr_expr.tr_paren_set _ id sd _ _ _ _ _ _ _
          (tr_expr_monotone _ _ _ _ _ _ _ h2 tmp hi2) hin

private theorem pg4376_invariant_set {ce : composite_env} {le : ttemp_env}
    {dst : destination} {r : cexpr} {sl : List Clight.statement}
    {a : Clight.expr} {tmp : List ident} (htr : tr_expr ce le dst r sl a tmp)
    (id : ident) (v : val) (hn : id ∉ tmp) :
    tr_expr ce (PTree.set id v le) dst r sl a tmp := by
  apply tr_expr_invariant _ _ _ _ _ _ _ htr
  intro x hx
  apply PTree.gso
  intro heq
  exact hn (heq ▸ hx)

private theorem pg4376_assign (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m m' : mem) (l r : cexpr)
    (b : block) (ofs : ptrofs) (bf : bitfield) (t : trace) (v v1 v' : val)
    (hl : eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf)
    (hr : eval_simple_rvalue (Csem.globalenv p) e m r v)
    (hcast : sem_cast v (Csyntax.typeof r) (Csyntax.typeof l) m = some v1)
    (ha : Csem.assign_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v1 t m' v') :
    pg4376Local xi p tp e m (.Eassign l r (Csyntax.typeof l)) t m'
      (.Eval v' (Csyntax.typeof l)) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_assign_effects _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 bf' any tmp h1 h2 hd hi1 hi2 hbf =>
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue p tp hp cu e m r v hr
      le .For_val sl2 a2 tmp2 h2
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    refine ⟨le, [], Or.inl ?_, tr_expr.tr_val_effect _ _ _ _ _, fun _ _ => rfl⟩
    apply plus_two
    · exact Clight.step_skip_seq _ _ _ _ _ _
    · exact step_make_assign xi p tp hp a1 a2 _ m b ofs bf t v1 m' v' v e le tf tk
        ha hev1 hev2 (hty2 ▸ hcast) hty1.symm
    · rfl
  | tr_assign_val dst _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 id tmp ty1 ty2 bf'
      h1 h2 hi1 hi2 hd hin hn1 hn2 ht1 ht2 hbf =>
    subst ty1 ty2
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue p tp hp cu e m r v hr
      le .For_val sl2 a2 tmp2 h2
    have hev1' := (tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      _ [] a1 tmp1 (pg4376_invariant_set h1 id v1 hn1)).2.2
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    refine ⟨PTree.set id v1 le, final dst (make_assign_value bf (.Etempvar id (Csyntax.typeof l))),
      Or.inl ?_, ?_, pg4376_set_agree _ _ _ _ hin⟩
    · apply plus_four
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · exact Clight.step_set _ _ _ _ _ _ _ _ (.cast _ _ _ _ hev2 (hty2 ▸ hcast))
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · exact step_make_assign xi p tp hp a1 (.Etempvar id (Csyntax.typeof l)) _ m b ofs bf t v1 m' v' v1
          e _ tf _ ha hev1' (.eval_Etempvar _ _ _ (PTree.gss _ _ _))
          (cast_idempotent _ _ _ _ _ hcast) hty1.symm
      · rfl
    · apply tr_val_gen
      · exact typeof_make_assign_value bf _
      · intro tge e' le' m'' hagree
        exact make_assign_value_sound p _ m b ofs bf v1 t m' v' ha tge e' le' m''
          (.Etempvar id (Csyntax.typeof l)) rfl (pg4376_temp_eval le tmp id v1 _ hin _ _ _ _ hagree)

private theorem pg4376_invariant_disjoint {ce : composite_env} {le le' : ttemp_env}
    {dst : destination} {r : cexpr} {sl : List Clight.statement}
    {a : Clight.expr} {tmp tmp' : List ident} (htr : tr_expr ce le dst r sl a tmp)
    (hd : CompCert4Lean.Lib.Coqlib.list_disjoint tmp tmp')
    (hagree : ∀ x, x ∉ tmp' → PTree.get x le' = PTree.get x le) :
    tr_expr ce le' dst r sl a tmp := by
  apply tr_expr_invariant _ _ _ _ _ _ _ htr
  intro x hx
  apply hagree
  intro hx'
  exact hd x x hx hx' rfl

private theorem pg4376_assignop (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m m' : mem) (op : binary_operation)
    (l r : cexpr) (tyres : ctype) (b : block) (ofs : ptrofs) (bf : bitfield)
    (t1 t2 : trace) (v1 v2 v3 v4 v' : val)
    (hl : eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf)
    (hderef : Csem.deref_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t1 v1)
    (hr : eval_simple_rvalue (Csem.globalenv p) e m r v2)
    (hop : sem_binary_operation (Csem.globalenv p).genv_cenv op v1 (Csyntax.typeof l)
      v2 (Csyntax.typeof r) m = some v3)
    (hcast : sem_cast v3 tyres (Csyntax.typeof l) m = some v4)
    (ha : Csem.assign_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v4 t2 m' v') :
    pg4376Local xi p tp e m (.Eassignop op l r tyres (Csyntax.typeof l)) (Eapp t1 t2) m'
      (.Eval v' (Csyntax.typeof l)) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_assignop_effects _ _ _ _ _ ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf' sl3 a3 tmp3 any tmp
      h1 h2 ht1 h3 hd12 hd13 hd23 hi1 hi2 hi3 hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue p tp hp cu e m r v2 hr
      le .For_val sl2 a2 tmp2 h2
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    obtain ⟨le', hex, hev3, hty3, hagree⟩ := step_tr_rvalof xi p tp hp cu hlink _ m b ofs bf t1 v1
      e le a1 sl3 a3 tmp3 tf (.Kseq (make_assign bf a1 (.Ebinop op a3 a2 tyres)) tk)
      hderef hev1 h3 hty1.symm
    have hev1' := (tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      _ [] a1 tmp1 (pg4376_invariant_disjoint h1 hd13 hagree)).2.2
    have hev2' := (tr_simple_rvalue p tp hp cu e m r v2 hr
      _ .For_val [] a2 tmp2 (pg4376_invariant_disjoint h2 hd23 hagree)).2.2
    refine ⟨le', [], Or.inl ?_, tr_expr.tr_val_effect _ _ _ _ _, ?_⟩
    · simp only [List.nil_append, Kseqlist_app sl3 [_] tk]
      apply star_plus_trans _ _ _ _ _ _ _ _ _ _ hex
      · apply plus_two
        · exact Clight.step_skip_seq _ _ _ _ _ _
        · apply step_make_assign xi p tp hp a1 (.Ebinop op a3 a2 tyres) _ m b ofs bf t2 v4 m' v' v3
            e le' tf tk ha hev1' _ hcast hty1.symm
          apply Clight.eval_expr.binary _ _ _ _ _ _ _ hev3 hev2'
          simpa only [hty3, ← hty1, ← hty2, comp_env_preserved p tp hp] using hop
        · rfl
      · rfl
    · intro x hx
      exact hagree x (fun hin => hx (hi3 x hin))
  | tr_assignop_val dst _ _ _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 id bf' tmp ty1
      h1 h2 h3 hd12 hd13 hd23 hi1 hi2 hi3 hin hn1 hn2 hn3 ht1 hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue p tp hp cu e m r v2 hr
      le .For_val sl2 a2 tmp2 h2
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    obtain ⟨le', hex, hev3, hty3, hagree⟩ := step_tr_rvalof xi p tp hp cu hlink _ m b ofs bf t1 v1
      e le a1 sl3 a3 tmp3 tf
      (Kseqlist (.Sset id (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)) ::
        make_assign bf a1 (.Etempvar id (Csyntax.typeof l)) ::
        final dst (make_assign_value bf (.Etempvar id (Csyntax.typeof l)))) tk)
      hderef hev1 h3 hty1.symm
    have h1' := pg4376_invariant_disjoint h1 hd13 hagree
    have hev1' := (tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      _ [] a1 tmp1 (pg4376_invariant_set h1' id v4 hn1)).2.2
    have hev2' := (tr_simple_rvalue p tp hp cu e m r v2 hr
      _ .For_val [] a2 tmp2 (pg4376_invariant_disjoint h2 hd23 hagree)).2.2
    refine ⟨PTree.set id v4 le', final dst (make_assign_value bf (.Etempvar id (Csyntax.typeof l))),
      Or.inl ?_, ?_, ?_⟩
    · simp only [List.nil_append, Kseqlist_app sl3 (_ :: _ :: _) tk]
      apply star_plus_trans _ _ _ _ _ _ _ _ _ _ hex
      · apply plus_four
        · exact Clight.step_skip_seq _ _ _ _ _ _
        · apply Clight.step_set
          apply Clight.eval_expr.cast _ _ _ _ _ hcast
          apply Clight.eval_expr.binary _ _ _ _ _ _ _ hev3 hev2'
          simpa only [hty3, ← hty1, ← hty2, comp_env_preserved p tp hp] using hop
        · exact Clight.step_skip_seq _ _ _ _ _ _
        · exact step_make_assign xi p tp hp a1 (.Etempvar id (Csyntax.typeof l)) _ m b ofs bf t2 v4 m' v' v4
            e _ tf _ ha hev1' (.eval_Etempvar _ _ _ (PTree.gss _ _ _))
            (cast_idempotent _ _ _ _ _ hcast) hty1.symm
        · rfl
      · rfl
    · apply tr_val_gen
      · exact typeof_make_assign_value bf _
      · intro tge e' le'' m'' hagree'
        exact make_assign_value_sound p _ m b ofs bf v4 t2 m' v' ha tge e' le'' m''
          (.Etempvar id (Csyntax.typeof l)) rfl (pg4376_temp_eval le' tmp id v4 _ hin _ _ _ _ hagree')
    · intro x hx
      exact (pg4376_set_agree le' tmp id v4 hin x hx).trans
        (hagree x (fun hin => hx (hi3 x hin)))

private theorem pg4376_incr_eval (p : cprogram) (tp : tprogram) (hp : match_prog p tp)
    (id : incr_or_decr) (e : cenv) (le : ttemp_env) (m : mem)
    (a : Clight.expr) (ty : ctype) (v v' : val)
    (hev : Clight.eval_expr (Clight.globalenv tp) e le m a v)
    (htype : Clight.typeof a = ty)
    (hincr : sem_incrdecr (Csem.globalenv p).genv_cenv id v ty m = some v') :
    Clight.eval_expr (Clight.globalenv tp) e le m (transl_incrdecr id a ty) v' := by
  cases id <;> simp only [transl_incrdecr] <;>
    apply Clight.eval_expr.binary _ _ _ _ _ _ _ hev (.const_int _ _) <;>
    rw [htype, comp_env_preserved p tp hp] <;> exact hincr

private theorem pg4376_postincr (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m m' : mem) (id : incr_or_decr) (l : cexpr)
    (b : block) (ofs : ptrofs) (bf : bitfield) (t1 t2 : trace) (v1 v2 v3 v' : val)
    (hl : eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf)
    (hderef : Csem.deref_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t1 v1)
    (hop : sem_incrdecr (Csem.globalenv p).genv_cenv id v1 (Csyntax.typeof l) m = some v2)
    (hcast : sem_cast v2 (incrdecr_type (Csyntax.typeof l)) (Csyntax.typeof l) m = some v3)
    (ha : Csem.assign_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf v3 t2 m' v') :
    pg4376Local xi p tp e m (.Epostincr id l (Csyntax.typeof l)) (Eapp t1 t2) m'
      (.Eval v1 (Csyntax.typeof l)) := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_postincr_effects _ _ _ ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf' any tmp
      h1 h2 ht1 hi1 hi2 hd hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    obtain ⟨le', hex, hev2, hty2, hagree⟩ := step_tr_rvalof xi p tp hp cu hlink _ m b ofs bf t1 v1
      e le a1 sl2 a2 tmp2 tf (.Kseq (make_assign bf a1 (transl_incrdecr id a2 (Csyntax.typeof l))) tk)
      hderef hev1 h2 hty1.symm
    have hev1' := (tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      _ [] a1 tmp1 (pg4376_invariant_disjoint h1 hd hagree)).2.2
    refine ⟨le', [], Or.inl ?_, tr_expr.tr_val_effect _ _ _ _ _, ?_⟩
    · simp only [List.nil_append, Kseqlist_app sl2 [_] tk]
      apply star_plus_trans _ _ _ _ _ _ _ _ _ _ hex
      · apply plus_two
        · exact Clight.step_skip_seq _ _ _ _ _ _
        · apply step_make_assign xi p tp hp a1 (transl_incrdecr id a2 (Csyntax.typeof l)) _ m b ofs bf t2 v3 m' v' v2
            e le' tf tk ha hev1' _ _ hty1.symm
          · exact pg4376_incr_eval p tp hp id e le' m a2 _ v1 v2 hev2 (hty2.trans hty1.symm) hop
          · cases id <;> exact hcast
        · rfl
      · rfl
    · intro x hx
      exact hagree x (fun hin => hx (hi2 x hin))
  | tr_postincr_val dst _ _ _ sl1 a1 tmp1 bf' temp ty1 tmp h1 hi1 hin hn1 ht1 hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    have hev1' := (tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      _ [] a1 tmp1 (pg4376_invariant_set h1 temp v1 hn1)).2.2
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    refine ⟨PTree.set temp v1 le, final dst (.Etempvar temp (Csyntax.typeof l)),
      Or.inl ?_, ?_, pg4376_set_agree _ _ _ _ hin⟩
    · apply plus_four
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · exact step_make_set xi p tp hp temp a1 _ m b ofs bf t1 v1 e le tf _ hderef hev1 hty1.symm
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · apply step_make_assign xi p tp hp a1 (transl_incrdecr id (.Etempvar temp (Csyntax.typeof l)) (Csyntax.typeof l))
          _ m b ofs bf t2 v3 m' v' v2 e _ tf _ ha hev1' _ _ hty1.symm
        · exact pg4376_incr_eval p tp hp id e _ m _ _ v1 v2
            (.eval_Etempvar _ _ _ (PTree.gss _ _ _)) rfl hop
        · cases id <;> exact hcast
      · rfl
    · exact tr_val_gen _ _ _ _ _ _ _ rfl (pg4376_temp_eval _ _ _ _ _ hin)

private def pg4376Prefix (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (e : cenv) (m : mem) (r : cexpr) (t : trace) : Prop :=
  ∀ (cu : cprogram), Ctypes.linkorder_program cu p →
  ∀ le dst sl a tmp, tr_expr cu.prog_comp_env le dst r sl a tmp →
  ∀ tf tk, ∃ s', star (Clight.step1 xi) (Clight.globalenv tp)
    (.State tf .Sskip (Kseqlist sl tk) e le m) t s'

private theorem pg4376_stuck_lift (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (e : cenv) (m : mem) (r : cexpr) (t : trace)
    (hnot : ∀ v ty, r ≠ .Eval v ty)
    (hlocal : pg4376Prefix xi p tp e m r t)
    (f : cfunction) (k : ccont) (C : cexpr → cexpr)
    (hc : leftcontext .RV .RV C) (s : tstate)
    (hs : match_states p tp (.ExprState f (C r) k e m) s) :
    ∃ s', (plus (Clight.step1 xi) (Clight.globalenv tp) s t s' ∨
      (star (Clight.step1 xi) (Clight.globalenv tp) s t s' ∧
       measure .Stuckstate < measure (.ExprState f (C r) k e m))) ∧
      match_states p tp .Stuckstate s' := by
  cases hs with
  | match_exprstates _ _ _ _ _ tf sl tk le dst a tmp cu hlink htf htr hmk =>
    obtain ⟨dst1, sl1, sl2, a1, tmp1, htr1, hsl, hinc, hrec⟩ :=
      tr_top_leftcontext tp cu e le m dst (C r) sl a tmp htr r C rfl hc
    have hr : tr_expr cu.prog_comp_env le dst1 r sl1 a1 tmp1 := by
      cases htr1 with
      | tr_top_val_val v ty _ _ _ _ => exact False.elim (hnot v ty rfl)
      | tr_top_base _ _ _ _ _ h => exact h
    obtain ⟨s', hex⟩ := hlocal cu hlink le dst1 sl1 a1 tmp1 hr tf (Kseqlist sl2 tk)
    subst sl
    refine ⟨s', Or.inr ⟨?_, by simp only [measure]; omega⟩, .match_stuckstate _⟩
    simpa only [Kseqlist_app sl1 sl2 tk] using hex

private theorem pg4376_assignop_prefix (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (op : binary_operation)
    (l r : cexpr) (tyres : ctype) (b : block) (ofs : ptrofs) (bf : bitfield)
    (t : trace) (v1 v2 : val)
    (hl : eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf)
    (hderef : Csem.deref_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t v1)
    (hr : eval_simple_rvalue (Csem.globalenv p) e m r v2) :
    pg4376Prefix xi p tp e m (.Eassignop op l r tyres (Csyntax.typeof l)) t := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_assignop_effects _ _ _ _ _ ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf' sl3 a3 tmp3 any tmp
      h1 h2 ht1 h3 hd12 hd13 hd23 hi1 hi2 hi3 hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue p tp hp cu e m r v2 hr
      le .For_val sl2 a2 tmp2 h2
    obtain ⟨le', hex, _⟩ := step_tr_rvalof xi p tp hp cu hlink _ m b ofs bf t v1
      e le a1 sl3 a3 tmp3 tf (.Kseq (make_assign bf' a1 (.Ebinop op a3 a2 tyres)) tk)
      hderef hev1 h3 hty1.symm
    refine ⟨.State tf .Sskip (.Kseq (make_assign bf' a1 (.Ebinop op a3 a2 tyres)) tk) e le' m, ?_⟩
    simpa only [List.nil_append, Kseqlist_app sl3 [_] tk, Kseqlist] using hex
  | tr_assignop_val dst _ _ _ _ _ sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 id bf' tmp ty1
      h1 h2 h3 hd12 hd13 hd23 hi1 hi2 hi3 hin hn1 hn2 hn3 ht1 hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨rfl, hty2, hev2⟩ := tr_simple_rvalue p tp hp cu e m r v2 hr
      le .For_val sl2 a2 tmp2 h2
    obtain ⟨le', hex, _⟩ := step_tr_rvalof xi p tp hp cu hlink _ m b ofs bf t v1
      e le a1 sl3 a3 tmp3 tf
      (Kseqlist (.Sset id (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)) ::
        make_assign bf' a1 (.Etempvar id (Csyntax.typeof l)) ::
        final dst (make_assign_value bf' (.Etempvar id (Csyntax.typeof l)))) tk)
      hderef hev1 h3 hty1.symm
    refine ⟨.State tf .Sskip
      (Kseqlist (.Sset id (.Ecast (.Ebinop op a3 a2 tyres) (Csyntax.typeof l)) ::
        make_assign bf' a1 (.Etempvar id (Csyntax.typeof l)) ::
        final dst (make_assign_value bf' (.Etempvar id (Csyntax.typeof l)))) tk) e le' m, ?_⟩
    simpa only [List.nil_append, Kseqlist_app sl3 (_ :: _ :: _) tk] using hex

private theorem pg4376_postincr_prefix (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m : mem) (id : incr_or_decr) (l : cexpr)
    (b : block) (ofs : ptrofs) (bf : bitfield) (t : trace) (v : val)
    (hl : eval_simple_lvalue (Csem.globalenv p) e m l b ofs bf)
    (hderef : Csem.deref_loc (Csem.globalenv p) (Csyntax.typeof l) m b ofs bf t v) :
    pg4376Prefix xi p tp e m (.Epostincr id l (Csyntax.typeof l)) t := by
  intro cu hlink le dst sl a tmp htr tf tk
  cases htr with
  | tr_postincr_effects _ _ _ ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf' any tmp
      h1 h2 ht1 hi1 hi2 hd hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    obtain ⟨le', hex, _⟩ := step_tr_rvalof xi p tp hp cu hlink _ m b ofs bf t v
      e le a1 sl2 a2 tmp2 tf (.Kseq (make_assign bf' a1 (transl_incrdecr id a2 (Csyntax.typeof l))) tk)
      hderef hev1 h2 hty1.symm
    refine ⟨.State tf .Sskip (.Kseq (make_assign bf' a1 (transl_incrdecr id a2 (Csyntax.typeof l))) tk) e le' m, ?_⟩
    simpa only [List.nil_append, Kseqlist_app sl2 [_] tk, Kseqlist] using hex
  | tr_postincr_val dst _ _ _ sl1 a1 tmp1 bf' temp ty1 tmp h1 hi1 hin hn1 ht1 hbf =>
    subst ty1
    obtain ⟨rfl, hty1, hev1⟩ := tr_simple_lvalue p tp hp cu e m l b ofs bf hl
      le sl1 a1 tmp1 h1
    have heq := is_bitfield_access_sound p tp hp cu hlink e le m a1 b ofs bf bf' hev1 hbf
    subst bf'
    refine ⟨.State tf .Sskip
      (Kseqlist (make_assign bf a1 (transl_incrdecr id (.Etempvar temp (Csyntax.typeof l)) (Csyntax.typeof l)) ::
        final dst (.Etempvar temp (Csyntax.typeof l))) tk) e (PTree.set temp v le) m, ?_⟩
    apply star_two
    · exact Clight.step_skip_seq _ _ _ _ _ _
    · exact step_make_set xi p tp hp temp a1 _ m b ofs bf t v e le tf _ hderef hev1 hty1.symm
    · rfl

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.AST

private theorem pg4376_external (xi : ExternalCalls) (ef : external_function)
    (ge1 ge2 : CompCert4Lean.Common.Globalenvs.Senv.t) (vargs : List val) (m : mem)
    (t : trace) (v : val) (m' : mem)
    (heq : CompCert4Lean.Common.Globalenvs.Senv.equiv ge1 ge2)
    (hcall : external_call xi ef ge1 vargs m t v m') :
    external_call xi ef ge2 vargs m t v m' := by
  have hbe : ∀ name sg, builtin_or_external_sem xi name sg ge1 vargs m t v m' →
      builtin_or_external_sem xi name sg ge2 vargs m t v m' := by
    intro name sg h
    cases hlookup : CompCert4Lean.Common.Builtins.lookup_builtin_function name sg with
    | some bf =>
      simp only [builtin_or_external_sem, hlookup] at h ⊢
      cases h
      constructor
      assumption
    | none =>
      simp only [builtin_or_external_sem, hlookup] at h ⊢
      exact (external_functions_properties xi name sg).ec_symbols_preserved _ _ _ _ _ _ _ heq h
  cases ef with
  | EF_external name sg =>
    exact (external_functions_properties xi name sg).ec_symbols_preserved _ _ _ _ _ _ _ heq hcall
  | EF_builtin name sg => exact hbe name sg hcall
  | EF_runtime name sg => exact hbe name sg hcall
  | EF_vload chunk => exact (volatile_load_ok chunk).ec_symbols_preserved _ _ _ _ _ _ _ heq hcall
  | EF_vstore chunk => exact (volatile_store_ok chunk).ec_symbols_preserved _ _ _ _ _ _ _ heq hcall
  | EF_malloc => cases hcall; constructor <;> assumption
  | EF_free => cases hcall <;> constructor <;> assumption
  | EF_memcpy sz al => cases hcall; constructor <;> assumption
  | EF_annot kind text targs =>
    exact (extcall_annot_ok text targs).ec_symbols_preserved _ _ _ _ _ _ _ heq hcall
  | EF_annot_val kind text targ =>
    cases hcall with
    | extcall_annot_val_sem_intro varg m arg hmatch =>
      constructor
      exact eventval_match_preserved ge1 ge2 heq.2.1 heq.1 _ _ _ hmatch
  | EF_inline_asm text sg clobber =>
    exact (inline_assembly_properties xi text sg).ec_symbols_preserved _ _ _ _ _ _ _ heq hcall
  | EF_debug kind text targs => cases hcall; constructor

private theorem pg4376_builtin (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (e : cenv) (m m' : mem) (ef : external_function)
    (tyargs : List ctype) (args : cexprlist) (ty : ctype)
    (vargs : List val) (t : trace) (v : val)
    (heval : eval_simple_list (Csem.globalenv p) e m args tyargs vargs)
    (hcall : external_call xi ef (Genv.to_senv (Csem.globalenv p).genv_genv) vargs m t v m') :
    pg4376Local xi p tp e m (.Ebuiltin ef tyargs args ty) t m' (.Eval v ty) := by
  intro cu hlink le dst sl a tmp htr tf tk
  have hcall' := pg4376_external xi ef _ _ vargs m t v m' (senv_preserved p tp hp) hcall
  cases htr with
  | tr_builtin_effects _ _ _ _ sl al tmp1 any tmp h1 hi =>
    obtain ⟨rfl, hev⟩ := tr_simple_exprlist p tp hp cu le args sl al tmp1 h1 e m tyargs vargs heval
    refine ⟨le, [], Or.inl ?_, tr_expr.tr_val_effect _ _ _ _ _, fun _ _ => rfl⟩
    apply plus_two
    · exact Clight.step_skip_seq _ _ _ _ _ _
    · exact Clight.step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hev hcall'
    · rfl
  | tr_builtin_val dst _ _ _ _ sl al tmp1 id tmp hdst h1 hin hi =>
    obtain ⟨rfl, hev⟩ := tr_simple_exprlist p tp hp cu le args sl al tmp1 h1 e m tyargs vargs heval
    refine ⟨PTree.set id v le, final dst (.Etempvar id ty), Or.inl ?_, ?_,
      pg4376_set_agree _ _ _ _ hin⟩
    · apply plus_two
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · exact Clight.step_builtin _ (some id) _ _ _ _ _ _ _ _ _ _ _ hev hcall'
      · rfl
    · exact tr_val_gen _ _ _ _ _ _ _ rfl (pg4376_temp_eval _ _ _ _ _ hin)

private theorem pg4376_call (xi : ExternalCalls) (p : cprogram) (tp : tprogram)
    (hp : match_prog p tp) (f : cfunction) (C : cexpr → cexpr) (rf : cexpr)
    (args : cexprlist) (ty : ctype) (k : ccont) (e : cenv) (m : mem)
    (tyargs : List ctype) (tres : ctype) (cc : calling_convention)
    (vf : val) (vargs : List val) (fd : cfundef)
    (hc : leftcontext .RV .RV C)
    (hclass : classify_fun (Csyntax.typeof rf) = .fun_case_f tyargs tres cc)
    (hfun : eval_simple_rvalue (Csem.globalenv p) e m rf vf)
    (hargs : eval_simple_list (Csem.globalenv p) e m args tyargs vargs)
    (hfind : Genv.find_funct (Csem.globalenv p).genv_genv vf = some fd)
    (htype : Csyntax.type_of_fundef fd = .Tfunction tyargs tres cc)
    (s : tstate) (hs : match_states p tp (.ExprState f (C (.Ecall rf args ty)) k e m) s) :
    ∃ s', plus (Clight.step1 xi) (Clight.globalenv tp) s E0 s' ∧
      match_states p tp (.Callstate fd vargs (.Kcall f e C ty k) m) s' := by
  obtain ⟨cu', tfd, hfind', hfd, hlink'⟩ := functions_translated p tp hp vf fd hfind
  have htype' := (type_of_fundef_preserved cu' fd tfd hfd).trans htype
  cases hs with
  | match_exprstates _ _ _ _ _ tf sl tk le dst a tmp cu hlink htf htr hmk =>
    obtain ⟨dst1, sl1, sl2, a1, tmp1, htr1, hsl, hinc, hrec⟩ :=
      tr_top_leftcontext tp cu e le m dst (C (.Ecall rf args ty)) sl a tmp htr
        (.Ecall rf args ty) C rfl hc
    subst sl
    cases htr1 with
    | tr_top_base _ _ _ _ _ htr1 =>
      cases htr1 with
      | tr_call_effects _ _ _ slf af tmpf sla al tmpa any tmp1 hf ha hd hi1 hi2 =>
        obtain ⟨rfl, hty, hevf⟩ := tr_simple_rvalue p tp hp cu e m rf vf hfun
          le .For_val slf af tmpf hf
        obtain ⟨rfl, heva⟩ := tr_simple_exprlist p tp hp cu le args sla al tmpa ha e m tyargs vargs hargs
        refine ⟨.Callstate tfd vargs (.Kcall none tf e le (Kseqlist sl2 tk)) m, ?_, ?_⟩
        · apply plus_two
          · exact Clight.step_skip_seq _ _ _ _ _ _
          · exact Clight.step_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hty ▸ hclass) hevf heva hfind' htype'
          · rfl
        · apply match_states.match_callstates _ _ _ _ _ _ cu' hlink' hfd
          intro ce
          apply match_cont.match_Kcall f e C ty k none tf le sl2 tk a dst tmp cu ce hlink htf hc _ hmk
          intro v m'
          exact hrec le m' (.Eval v ty) [] (tr_expr.tr_val_effect _ _ _ _ _) (fun _ _ => rfl) rfl
      | tr_call_val dst1 _ _ _ slf af tmpf sla al tmpa id tmp1 hdst hf ha hd hin hi1 hi2 =>
        obtain ⟨rfl, hty, hevf⟩ := tr_simple_rvalue p tp hp cu e m rf vf hfun
          le .For_val slf af tmpf hf
        obtain ⟨rfl, heva⟩ := tr_simple_exprlist p tp hp cu le args sla al tmpa ha e m tyargs vargs hargs
        refine ⟨.Callstate tfd vargs
          (.Kcall (some id) tf e le (Kseqlist (final dst1 (.Etempvar id ty) ++ sl2) tk)) m, ?_, ?_⟩
        · apply plus_two
          · exact Clight.step_skip_seq _ _ _ _ _ _
          · exact Clight.step_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hty ▸ hclass) hevf heva hfind' htype'
          · rfl
        · apply match_states.match_callstates _ _ _ _ _ _ cu' hlink' hfd
          intro ce
          apply match_cont.match_Kcall f e C ty k (some id) tf le
            (final dst1 (.Etempvar id ty) ++ sl2) tk a dst tmp cu ce hlink htf hc _ hmk
          intro v m'
          exact hrec (PTree.set id v le) m' (.Eval v ty) (final dst1 (.Etempvar id ty))
            (tr_val_gen _ _ _ _ _ _ _ rfl (pg4376_temp_eval _ _ _ _ _ hin))
            (pg4376_set_agree _ _ _ _ hin) rfl

set_option maxHeartbeats 1600000 in
 theorem estep_simulation : estep_simulationStatement := by
  intro xi p tp hp S1 t S2 hstep s hs
  cases hstep with
  | @step_expr f r k e m v ty heval hnot hty =>
    subst ty
    exact pg4376_expr xi p tp hp f r k e m v heval (by cases r <;> exact hnot) s hs
  | @step_rvalof_volatile f C l ty k e m b ofs bf t v hc hl hd ht hv =>
    subst ty
    exact pg4376_lift xi p tp e m (.Evalof l (Csyntax.typeof l)) t m (.Eval v (Csyntax.typeof l))
      (by intro v ty h; cases h) rfl
      (pg4376_volatile xi p tp hp e m l b ofs bf t v hl hd hv) f k C hc s hs
  | @step_seqand_true f C r1 r2 ty k e m v hc hr hb =>
    exact pg4376_lift xi p tp e m (.Eseqand r1 r2 ty) E0 m (.Eparen r2 type_bool ty)
      (by intro v ty h; cases h) rfl
      (pg4376_seqand_continue xi p tp hp e m r1 r2 ty v hr hb) f k C hc s hs
  | @step_seqand_false f C r1 r2 ty k e m v hc hr hb =>
    exact pg4376_lift xi p tp e m (.Eseqand r1 r2 ty) E0 m (.Eval (.Vint Lib.Integers.Int.zero) ty)
      (by intro v ty h; cases h) rfl
      (pg4376_seqand_stop xi p tp hp e m r1 r2 ty v hr hb) f k C hc s hs
  | @step_seqor_true f C r1 r2 ty k e m v hc hr hb =>
    exact pg4376_lift xi p tp e m (.Eseqor r1 r2 ty) E0 m (.Eval (.Vint Lib.Integers.Int.one) ty)
      (by intro v ty h; cases h) rfl
      (pg4376_seqor_stop xi p tp hp e m r1 r2 ty v hr hb) f k C hc s hs
  | @step_seqor_false f C r1 r2 ty k e m v hc hr hb =>
    exact pg4376_lift xi p tp e m (.Eseqor r1 r2 ty) E0 m (.Eparen r2 type_bool ty)
      (by intro v ty h; cases h) rfl
      (pg4376_seqor_continue xi p tp hp e m r1 r2 ty v hr hb) f k C hc s hs
  | @step_condition f C r1 r2 r3 ty k e m v b hc hr hb =>
    exact pg4376_lift xi p tp e m (.Econdition r1 r2 r3 ty) E0 m (.Eparen (if b then r2 else r3) ty ty)
      (by intro v ty h; cases h) rfl
      (pg4376_condition xi p tp hp e m r1 r2 r3 ty v b hr hb) f k C hc s hs
  | @step_assign f C l r ty k e m b ofs bf v v1 t m' v' hc hl hr hcast ha ht =>
    subst ty
    exact pg4376_lift xi p tp e m (.Eassign l r (Csyntax.typeof l)) t m' (.Eval v' (Csyntax.typeof l))
      (by intro v ty h; cases h) rfl
      (pg4376_assign xi p tp hp e m m' l r b ofs bf t v v1 v' hl hr hcast ha) f k C hc s hs
  | @step_assignop f C op l r tyres ty k e m b ofs bf v1 v2 v3 v4 t1 t2 m' v' t
      hc hl hd hr hop hcast ha ht htrace =>
    subst ty t
    exact pg4376_lift xi p tp e m (.Eassignop op l r tyres (Csyntax.typeof l)) (Eapp t1 t2) m'
      (.Eval v' (Csyntax.typeof l)) (by intro v ty h; cases h) rfl
      (pg4376_assignop xi p tp hp e m m' op l r tyres b ofs bf t1 t2 v1 v2 v3 v4 v'
        hl hd hr hop hcast ha) f k C hc s hs
  | @step_assignop_stuck f C op l r tyres ty k e m b ofs bf v1 v2 t hc hl hd hr hstuck ht =>
    subst ty
    exact pg4376_stuck_lift xi p tp e m (.Eassignop op l r tyres (Csyntax.typeof l)) t
      (by intro v ty h; cases h)
      (pg4376_assignop_prefix xi p tp hp e m op l r tyres b ofs bf t v1 v2 hl hd hr) f k C hc s hs
  | @step_postincr f C id l ty k e m b ofs bf v1 v2 v3 t1 t2 m' v' t hc hl hd hop hcast ha ht htrace =>
    subst ty t
    exact pg4376_lift xi p tp e m (.Epostincr id l (Csyntax.typeof l)) (Eapp t1 t2) m'
      (.Eval v1 (Csyntax.typeof l)) (by intro v ty h; cases h) rfl
      (pg4376_postincr xi p tp hp e m m' id l b ofs bf t1 t2 v1 v2 v3 v' hl hd hop hcast ha)
      f k C hc s hs
  | @step_postincr_stuck f C id l ty k e m b ofs bf v1 t hc hl hd hstuck ht =>
    subst ty
    exact pg4376_stuck_lift xi p tp e m (.Epostincr id l (Csyntax.typeof l)) t
      (by intro v ty h; cases h)
      (pg4376_postincr_prefix xi p tp hp e m id l b ofs bf t v1 hl hd) f k C hc s hs
  | @step_comma f C r1 r2 ty k e m v hc hr ht =>
    exact pg4376_lift xi p tp e m (.Ecomma r1 r2 ty) E0 m r2
      (by intro v ty h; cases h) ht.symm
      (pg4376_comma xi p tp hp e m r1 r2 ty v hr) f k C hc s hs
  | @step_paren f C r tycast ty k e m v1 v hc hr hcast =>
    exact pg4376_lift xi p tp e m (.Eparen r tycast ty) E0 m (.Eval v ty)
      (by intro v ty h; cases h) rfl
      (pg4376_paren xi p tp hp e m r tycast ty v1 v hr hcast) f k C hc s hs
  | @step_call f C rf args ty k e m tyargs tres cc vf vargs fd hc hclass hf ha hfind ht =>
    obtain ⟨s', hex, hm⟩ := pg4376_call xi p tp hp f C rf args ty k e m tyargs tres cc vf vargs fd
      hc hclass hf ha hfind ht s hs
    exact ⟨s', Or.inl hex, hm⟩
  | @step_builtin f C ef tyargs args ty k e m vargs t v m' hc ha hcall =>
    exact pg4376_lift xi p tp e m (.Ebuiltin ef tyargs args ty) t m' (.Eval v ty)
      (by intro v ty h; cases h) rfl
      (pg4376_builtin xi p tp hp e m m' ef tyargs args ty vargs t v ha hcall) f k C hc s hs

end
end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.SimplExprspec

theorem transl_initial_states :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      transl_initial_statesStatement := by
  intro binary64_certificate binary32_certificate
  letI : Linker cprogram :=
    Ctypes.Linker_program cfunction Ctypes.linker_program_certificate_proof
  intro p tp hmatch S hinit
  cases hinit with
  | @intro b f m0 hmem hsymbol hfun htype =>
      obtain ⟨cu, tf, hfind, htr, hlink⟩ :=
        function_ptr_translated p tp hmatch b f hfun
      have hmatchgen :=
        (pg3898_match_iff Ctypes.linker_program_certificate_proof p tp).mp hmatch
      have hmem' : CompCert4Lean.Common.Globalenvs.Genv.init_mem
          (Ctypes.program_of_program tp) = some m0 := by
        exact @CompCert4Lean.Common.Globalenvs.Genv.init_mem_match
          cprogram cfundef ctype tfundef ctype
          (Ctypes.Linker_program cfunction Ctypes.linker_program_certificate_proof)
          tr_fundef Eq p (Ctypes.program_of_program p)
          (Ctypes.program_of_program tp) hmatchgen.1 m0 hmem
      have hmain : tp.prog_main = p.prog_main := hmatch.1.2.1
      have hsymbol' :
          CompCert4Lean.Common.Globalenvs.Genv.find_symbol
              (CompCert4Lean.Common.Globalenvs.Genv.globalenv
                (Ctypes.program_of_program tp)) tp.prog_main =
            some b := by
        rw [hmain]
        exact (symbols_preserved p tp hmatch p.prog_main).trans hsymbol
      have htype' : Clight.type_of_fundef tf = Csyntax.type_of_fundef f :=
        type_of_fundef_preserved cu f tf htr
      refine ⟨.Callstate tf [] .Kstop m0, ?_, ?_⟩
      · exact Clight.initial_state.intro b tf m0 hmem' hsymbol' hfind (htype'.trans htype)
      · apply match_states.match_callstates _ _ _ _ _ _ cu hlink htr
        intro ce
        exact match_cont.match_Kstop ce

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Linking

open CompCert4Lean.Common.AST
open CompCert4Lean.Cfrontend.SimplExprspec

theorem transf_program_match
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transf_program_matchStatement := by
  intro context source target success
  let certificate := Ctypes.linker_program_certificate_proof
  letI : Linker cprogram := Ctypes.Linker_program cfunction certificate
  unfold SimplExpr.transl_program at success
  cases translation : transform_partial_program
      (SimplExpr.transl_fundef context source.prog_comp_env)
      (Ctypes.program_of_program source) with
  | Error message => simp [translation] at success
  | OK translated =>
    simp only [translation] at success
    cases success
    apply (pg3898_match_iff certificate _ _).mpr
    refine ⟨?_, rfl⟩
    apply match_transform_partial_program2
      (LF := Ctypes.Linker_fundef cfunction) (LV := Ctypes.Linker_types) tr_fundef Eq
      (fun _ definition => SimplExpr.transl_fundef context source.prog_comp_env definition)
      (fun _ value => .OK value) source (Ctypes.program_of_program source) translated
    · exact translation
    · intro name definition translatedDefinition result
      exact SimplExprspec.transl_fundef_spec context source definition translatedDefinition result
    · intro name value translatedValue result
      cases result
      rfl

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.SimplExpr
open CompCert4Lean.Cfrontend.SimplExprspec
open CompCert4Lean.Lib.Maps

section

variable [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
  [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]

set_option maxHeartbeats 8000000 in
theorem sstep_simulation : sstep_simulationStatement := by
  intro external source target programs before events after stepped translated matched
  cases stepped <;> cases matched
  case do₁ func expression continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_do _ _ expressionMatch =>
      cases expressionMatch with
      | tr_expr_stmt_intro statements result temporaryNames expressionMatch =>
        refine ⟨_, Or.inr ⟨push_seq external target _ _ _ _ _ _, ?_⟩, ?_⟩
        · simp only [measure]
          omega
        · exact .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked functionMatch
            (expressionMatch _ _ _ _) (.match_Kdo _ _ _ _ contMatch)
  case do₂ func value exprType continuation environment memory
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kdo _ _ _ _ contMatch =>
      cases expressionMatch with
      | tr_top_base _ _ _ _ _ valueMatch =>
        cases valueMatch
        exact ⟨_, Or.inr ⟨star_refl _ _ _, by simp [measure, esize]⟩,
          .match_regularstates _ _ _ _ _ _ _ _ temps unit linked functionMatch .tr_skip contMatch⟩
  case sequence func first second continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_seq _ _ translatedFirst translatedSecond firstMatch secondMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch firstMatch (.match_Kseq _ _ _ _ _ secondMatch contMatch)⟩
      apply plus_one
      exact Clight.step_seq _ _ _ _ _ _ _
  case skipSequence func statement continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kseq _ _ _ _ _ stmtMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch stmtMatch contMatch⟩
      apply plus_one
      exact Clight.step_skip_seq _ _ _ _ _ _
  case continueSequence func statement continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kseq _ _ _ _ _ stmtMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_continue contMatch⟩
      apply plus_one
      exact Clight.step_continue_seq _ _ _ _ _ _
  case breakSequence func statement continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kseq _ _ _ _ _ stmtMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_break contMatch⟩
      apply plus_one
      exact Clight.step_break_seq _ _ _ _ _ _
  case ifStart func condition first second continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_ifthenelse_empty _ _ result expressionMatch =>
      cases expressionMatch with
      | tr_expression_intro statements _ temporaryNames expressionMatch =>
        refine ⟨_, Or.inl ?_, .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked
          functionMatch (expressionMatch _ _ _ _) (.match_Kifthenelse_empty _ _ _ _ contMatch)⟩
        exact plus_left _ E0 (Clight.step_seq _ _ _ _ _ _ _)
          (push_seq external target _ _ _ _ _ _) rfl
    | tr_ifthenelse _ _ _ _ result translatedFirst translatedSecond expressionMatch firstMatch secondMatch =>
      cases expressionMatch with
      | tr_expression_intro statements _ temporaryNames expressionMatch =>
        refine ⟨_, Or.inl ?_, .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked
          functionMatch (expressionMatch _ _ _ _)
          (.match_Kifthenelse_1 _ _ _ _ _ _ _ _ firstMatch secondMatch contMatch)⟩
        exact plus_left _ E0 (Clight.step_seq _ _ _ _ _ _ _)
          (push_seq external target _ _ _ _ _ _) rfl
  case ifFinish func value exprType first second continuation environment memory choice boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kifthenelse_empty _ _ _ translatedCont contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      cases choice <;>
        refine ⟨_, Or.inr ⟨?_, by simp [measure, esize]⟩,
          .match_regularstates _ _ _ _ _ _ _ _ temps unit linked functionMatch .tr_skip contMatch⟩ <;>
        apply star_one <;> exact Clight.step_skip_seq _ _ _ _ _ _
    | match_Kifthenelse_1 _ _ _ _ _ translatedFirst translatedSecond translatedCont
        firstMatch secondMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨.State translatedFunc (if choice then translatedFirst else translatedSecond)
        translatedCont environment temps memory, Or.inl ?_, ?_⟩
      · apply plus_two
        · exact Clight.step_skip_seq _ _ _ _ _ _
        · exact Clight.step_ifthenelse _ _ _ _ _ _ _ _ _ _ evaluated (typed ▸ boolean)
        · rfl
      · cases choice <;> exact .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
          functionMatch (by assumption) contMatch
  case whileStart func condition body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_while _ _ test translatedBody conditionMatch bodyMatch =>
      cases conditionMatch with
      | tr_if_intro statements result temporaryNames expressionMatch =>
        let test := makeseq (statements ++ [makeif result .Sskip .Sbreak])
        refine ⟨.State translatedFunc .Sskip
          (Kseqlist (statements ++ [makeif result .Sskip .Sbreak])
            (.Kseq translatedBody (.Kloop1 (.Ssequence test translatedBody) .Sskip translatedCont)))
          environment temps memory, Or.inl ?_, ?_⟩
        · exact plus_left _ E0 (Clight.step_loop _ _ _ _ _ _ _)
            (star_step _ E0 (Clight.step_seq _ _ _ _ _ _ _)
              (push_seq external target _ _ _ _ _ _) rfl) rfl
        · rw [Kseqlist_app]
          exact .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked functionMatch
            (expressionMatch _ _ _ _)
            (.match_Kwhile1 _ _ _ _ _ _ _ _
              (.tr_if_intro _ _ _ _ _ _ expressionMatch) bodyMatch contMatch)
  case whileFalse func value exprType condition body continuation environment memory boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kwhile1 _ _ _ _ test _ translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      refine plus_left _ E0 (Clight.step_skip_seq _ _ _ _ _ _) ?_ rfl
      apply star_trans
      · exact step_makeif external target _ _ _ _ _ _ _ _ _ false evaluated
          (by simpa only [typed] using boolean)
      · apply star_two
        · exact Clight.step_break_seq _ _ _ _ _ _
        · exact Clight.step_break_loop1 _ _ _ _ _ _ _
        · rfl
      · rfl
  case whileTrue func value exprType condition body continuation environment memory boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kwhile1 _ _ _ _ test _ translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch bodyMatch (.match_Kwhile2 _ _ _ _ _ _ _ conditionMatch bodyMatch contMatch)⟩
      refine plus_left _ E0 (Clight.step_skip_seq _ _ _ _ _ _) ?_ rfl
      apply star_right
      · exact step_makeif external target _ _ _ _ _ _ _ _ _ true evaluated
          (by simpa only [typed] using boolean)
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · rfl
  case whileNext func statement condition body continuation environment memory finished
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    have translatedFinished : translatedStmt = .Sskip ∨ translatedStmt = .Scontinue := by
      rcases finished with rfl | rfl <;> cases stmtMatch <;> simp
    cases contMatch with
    | match_Kwhile2 _ _ _ _ test translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch (.tr_while _ _ _ _ conditionMatch bodyMatch) contMatch⟩
      apply plus_two
      · exact Clight.step_skip_or_continue_loop1 _ _ _ _ _ _ _ _ translatedFinished
      · exact Clight.step_skip_loop2 _ _ _ _ _ _ _
      · rfl
  case whileBreak func condition body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kwhile2 _ _ _ _ test translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      apply plus_one
      exact Clight.step_break_loop1 _ _ _ _ _ _ _
  case dowhileStart func condition body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_dowhile _ _ test translatedBody conditionMatch bodyMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch bodyMatch (.match_Kdowhile1 _ _ _ _ _ _ _ conditionMatch bodyMatch contMatch)⟩
      apply plus_one
      exact Clight.step_loop _ _ _ _ _ _ _
  case dowhileTest func statement condition body continuation environment memory finished
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    have translatedFinished : translatedStmt = .Sskip ∨ translatedStmt = .Scontinue := by
      rcases finished with rfl | rfl <;> cases stmtMatch <;> simp
    cases contMatch with
    | match_Kdowhile1 _ _ _ _ test translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      cases conditionMatch with
      | tr_if_intro statements result temporaryNames expressionMatch =>
        let test := makeseq (statements ++ [makeif result .Sskip .Sbreak])
        refine ⟨.State translatedFunc .Sskip
          (Kseqlist (statements ++ [makeif result .Sskip .Sbreak])
            (.Kloop2 translatedBody test translatedCont)) environment temps memory, Or.inl ?_, ?_⟩
        · exact plus_left _ E0
            (Clight.step_skip_or_continue_loop1 _ _ _ _ _ _ _ _ translatedFinished)
            (push_seq external target _ _ _ _ _ _) rfl
        · rw [Kseqlist_app]
          exact .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked functionMatch
            (expressionMatch _ _ _ _)
            (.match_Kdowhile2 _ _ _ _ _ _ _ _
              (.tr_if_intro _ _ _ _ _ _ expressionMatch) bodyMatch contMatch)
  case dowhileFalse func value exprType condition body continuation environment memory boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kdowhile2 _ _ _ _ test _ translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      refine plus_left _ E0 (Clight.step_skip_seq _ _ _ _ _ _) ?_ rfl
      apply star_right
      · exact step_makeif external target _ _ _ _ _ _ _ _ _ false evaluated
          (by simpa only [typed] using boolean)
      · exact Clight.step_break_loop2 _ _ _ _ _ _ _
      · rfl
  case dowhileTrue func value exprType condition body continuation environment memory boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kdowhile2 _ _ _ _ test _ translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch (.tr_dowhile _ _ _ _ conditionMatch bodyMatch) contMatch⟩
      refine plus_left _ E0 (Clight.step_skip_seq _ _ _ _ _ _) ?_ rfl
      apply star_right
      · exact step_makeif external target _ _ _ _ _ _ _ _ _ true evaluated
          (by simpa only [typed] using boolean)
      · exact Clight.step_skip_loop2 _ _ _ _ _ _ _
      · rfl
  case dowhileBreak func condition body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kdowhile1 _ _ _ _ test translatedBody translatedCont conditionMatch bodyMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      apply plus_one
      exact Clight.step_break_loop1 _ _ _ _ _ _ _
  case forStart func initialization condition iteration body continuation environment memory nonempty
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_for_1 => exact False.elim (nonempty rfl)
    | tr_for_2 _ _ _ _ test translatedInit translatedIteration translatedBody
        conditionMatch nonempty initMatch iterationMatch bodyMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch initMatch (.match_Kseq _ _ _ _ _
          (.tr_for_1 _ _ _ _ _ _ conditionMatch iterationMatch bodyMatch) contMatch)⟩
      apply plus_one
      exact Clight.step_seq _ _ _ _ _ _ _
  case forTest func condition iteration body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_for_2 _ _ _ _ _ _ _ _ _ nonempty => exact False.elim (nonempty rfl)
    | tr_for_1 _ _ _ test translatedIteration translatedBody conditionMatch iterationMatch bodyMatch =>
      cases conditionMatch with
      | tr_if_intro statements result temporaryNames expressionMatch =>
        let test := makeseq (statements ++ [makeif result .Sskip .Sbreak])
        refine ⟨.State translatedFunc .Sskip
          (Kseqlist (statements ++ [makeif result .Sskip .Sbreak])
            (.Kseq translatedBody
              (.Kloop1 (.Ssequence test translatedBody) translatedIteration translatedCont)))
          environment temps memory, Or.inl ?_, ?_⟩
        · exact plus_left _ E0 (Clight.step_loop _ _ _ _ _ _ _)
            (star_step _ E0 (Clight.step_seq _ _ _ _ _ _ _)
              (push_seq external target _ _ _ _ _ _) rfl) rfl
        · rw [Kseqlist_app]
          exact .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked functionMatch
            (expressionMatch _ _ _ _)
            (.match_Kfor2 _ _ _ _ _ _ _ _ _ _
              (.tr_if_intro _ _ _ _ _ _ expressionMatch) iterationMatch bodyMatch contMatch)
  case forFalse func value exprType condition iteration body continuation environment memory boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kfor2 _ _ _ _ _ test _ translatedIteration translatedBody translatedCont
        conditionMatch iterationMatch bodyMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      refine plus_left _ E0 (Clight.step_skip_seq _ _ _ _ _ _) ?_ rfl
      apply star_trans
      · exact step_makeif external target _ _ _ _ _ _ _ _ _ false evaluated
          (by simpa only [typed] using boolean)
      · apply star_two
        · exact Clight.step_break_seq _ _ _ _ _ _
        · exact Clight.step_break_loop1 _ _ _ _ _ _ _
        · rfl
      · rfl
  case forTrue func value exprType condition iteration body continuation environment memory boolean
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kfor2 _ _ _ _ _ test _ translatedIteration translatedBody translatedCont
        conditionMatch iterationMatch bodyMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch bodyMatch
        (.match_Kfor3 _ _ _ _ _ _ _ _ _ conditionMatch iterationMatch bodyMatch contMatch)⟩
      refine plus_left _ E0 (Clight.step_skip_seq _ _ _ _ _ _) ?_ rfl
      apply star_right
      · exact step_makeif external target _ _ _ _ _ _ _ _ _ true evaluated
          (by simpa only [typed] using boolean)
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · rfl
  case forIter func statement condition iteration body continuation environment memory finished
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    have translatedFinished : translatedStmt = .Sskip ∨ translatedStmt = .Scontinue := by
      rcases finished with rfl | rfl <;> cases stmtMatch <;> simp
    cases contMatch with
    | match_Kfor3 _ _ _ _ _ translatedIteration test translatedBody translatedCont
        conditionMatch iterationMatch bodyMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch iterationMatch
        (.match_Kfor4 _ _ _ _ _ _ _ _ _ conditionMatch iterationMatch bodyMatch contMatch)⟩
      apply plus_one
      exact Clight.step_skip_or_continue_loop1 _ _ _ _ _ _ _ _ translatedFinished
  case forBreak func condition iteration body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kfor3 _ _ _ _ _ translatedIteration test translatedBody translatedCont
        conditionMatch iterationMatch bodyMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      apply plus_one
      exact Clight.step_break_loop1 _ _ _ _ _ _ _
  case forNext func condition iteration body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kfor4 _ _ _ _ _ translatedIteration test translatedBody translatedCont
        conditionMatch iterationMatch bodyMatch contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch (.tr_for_1 _ _ _ _ _ _ conditionMatch iterationMatch bodyMatch) contMatch⟩
      apply plus_one
      exact Clight.step_skip_loop2 _ _ _ _ _ _ _
  case returnNone func continuation environment memory freedMemory freed
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    refine ⟨_, Or.inl ?_, .match_returnstates _ _ _ _
      (match_cont_call_cont source target _ _ _ contMatch)⟩
    apply plus_one
    exact Clight.step_return_0 _ _ _ _ _ _
      (by rw [blocks_of_env_preserved source target programs environment]; exact freed)
  case returnSome func expression continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_return_some _ prelude result expressionMatch =>
      cases expressionMatch with
      | tr_expression_intro statements _ temporaryNames expressionMatch =>
        refine ⟨_, Or.inl ?_, .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked
          functionMatch (expressionMatch _ _ _ _) (.match_Kreturn _ _ _ _ contMatch)⟩
        exact plus_left _ E0 (Clight.step_seq _ _ _ _ _ _ _)
          (push_seq external target _ _ _ _ _ _) rfl
  case returnValue func value exprType continuation environment memory resultValue freedMemory casted freed
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kreturn _ _ _ translatedCont contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_returnstates _ _ _ _
        (match_cont_call_cont source target _ _ _ contMatch)⟩
      apply plus_two
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · exact Clight.step_return_1 _ _ _ _ _ _ _ _ _ evaluated
          (by simpa only [typed, function_return_preserved _ _ _ functionMatch] using casted)
          (by rw [blocks_of_env_preserved source target programs environment]; exact freed)
      · rfl
  case skipCall func continuation environment memory freedMemory callContinuation freed
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    have translatedCall : Clight.is_call_cont translatedCont := by
      cases contMatch <;> simp_all [Csem.is_call_cont, Clight.is_call_cont]
    refine ⟨_, Or.inl ?_, .match_returnstates _ _ _ _
      (match_cont_is_call_cont source target _ _ _ contMatch callContinuation)⟩
    apply plus_one
    exact Clight.step_skip_call _ _ _ _ _ _ translatedCall
      (by rw [blocks_of_env_preserved source target programs environment]; exact freed)
  case switchStart func expression labels continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_switch _ _ prelude result translatedLabels expressionMatch labelsMatch =>
      cases expressionMatch with
      | tr_expression_intro statements _ temporaryNames expressionMatch =>
        refine ⟨_, Or.inl ?_, .match_exprstates _ _ _ _ _ _ _ _ temps _ _ _ unit linked
          functionMatch (expressionMatch _ _ _ _) (.match_Kswitch1 _ _ _ _ _ _ labelsMatch contMatch)⟩
        exact plus_left _ E0 (Clight.step_seq _ _ _ _ _ _ _)
          (push_seq external target _ _ _ _ _ _) rfl
  case switchSelect func exprType labels continuation environment memory value index selected
      translatedFunc statements translatedCont temps destination result temporaryNames unit
      linked functionMatch contMatch expressionMatch =>
    cases contMatch with
    | match_Kswitch1 _ _ _ _ translatedLabels translatedCont labelsMatch contMatch =>
      obtain ⟨rfl, typed, evaluated⟩ :=
        tr_top_val_for_val_inv target _ _ _ _ _ _ _ _ _ expressionMatch
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked functionMatch
        (tr_seq_of_labeled_statement _ _ _ (tr_select_switch _ _ _ _ labelsMatch))
        (.match_Kswitch2 _ _ _ contMatch)⟩
      apply plus_two
      · exact Clight.step_skip_seq _ _ _ _ _ _
      · exact Clight.step_switch _ _ _ _ _ _ _ _ _ evaluated (by simpa only [typed] using selected)
      · rfl
  case switchFinish func statement continuation environment memory finished
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    have translatedFinished : translatedStmt = .Sskip ∨ translatedStmt = .Sbreak := by
      rcases finished with rfl | rfl <;> cases stmtMatch <;> simp
    cases contMatch with
    | match_Kswitch2 _ _ _ contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_skip contMatch⟩
      apply plus_one
      exact Clight.step_skip_break_switch _ _ _ _ _ _ translatedFinished
  case switchContinue func continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    cases contMatch with
    | match_Kswitch2 _ _ _ contMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch .tr_continue contMatch⟩
      apply plus_one
      exact Clight.step_continue_switch _ _ _ _ _
  case label func label body continuation environment memory
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch with
    | tr_label _ _ translatedBody bodyMatch =>
      refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
        functionMatch bodyMatch contMatch⟩
      apply plus_one
      exact Clight.step_label _ _ _ _ _ _ _
  case goto func label continuation environment memory nextBody nextCont found
      translatedFunc translatedStmt translatedCont temps unit linked functionMatch stmtMatch contMatch =>
    cases stmtMatch
    have bodyMatch : tr_stmt unit.prog_comp_env func.fn_body translatedFunc.fn_body := by
      cases functionMatch
      assumption
    have labelMatch := tr_find_label source target unit.prog_comp_env label
      func.fn_body (Csem.call_cont continuation) translatedFunc.fn_body (Clight.call_cont translatedCont)
      bodyMatch (match_cont_call_cont source target _ _ _ contMatch _)
    rw [found] at labelMatch
    obtain ⟨translatedBody, nextTranslatedCont, targetFound, stmtMatch, nextContMatch⟩ := labelMatch
    refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _ temps unit linked
      functionMatch stmtMatch nextContMatch⟩
    apply plus_one
    exact Clight.step_goto _ _ _ _ _ _ _ _ targetFound
  case internalFunction func arguments continuation memory environment allocatedMemory boundMemory
      distinct allocated bound translatedDefinition translatedCont unit linked definitionMatch contMatch =>
    cases definitionMatch with
    | tr_internal _ translatedFunc functionMatch =>
      have preserved := functionMatch
      cases functionMatch with
      | tr_function_intro bodyMatch returnMatch conventionMatch parametersMatch variablesMatch =>
        refine ⟨_, Or.inl ?_, .match_regularstates _ _ _ _ _ _ _ _
          (Clight.create_undef_temps translatedFunc.fn_temps) unit linked preserved bodyMatch (contMatch _)⟩
        apply plus_one
        apply Clight.step_internal_function
        apply Clight.function_entry1.intro allocatedMemory
        · simpa only [parametersMatch, variablesMatch, Clight.var_names, Csyntax.var_names] using distinct
        · simpa only [parametersMatch, variablesMatch, Csem.empty_env, Clight.empty_env] using
            alloc_variables_preserved source target programs _ _ _ _ _ allocated
        · simpa only [parametersMatch] using
            bind_parameters_preserved source target programs _ _ _ _ _ bound
        · rfl
  case externalFunction externalFunc argumentTypes returnType convention arguments continuation memory
      returned freedMemory called translatedDefinition translatedCont unit linked definitionMatch contMatch =>
    cases definitionMatch
    refine ⟨_, Or.inl ?_, .match_returnstates _ _ _ _ contMatch⟩
    apply plus_one
    exact Clight.step_external_function _ _ _ _ _ _ _ _ _ _
      (pg4376_external external externalFunc _ _ _ _ _ _ _
        (senv_preserved source target programs) called)
  case returnstate value func environment context exprType continuation memory translatedCont contMatch =>
    have callMatch := contMatch (PTree.empty _)
    cases callMatch with
    | match_Kcall _ _ _ _ _ resultId translatedFunc temps statements translatedCont
        result destination temporaryNames unit _ linked functionMatch contextMatch expressionMatch expressionContMatch =>
      refine ⟨_, Or.inl ?_, .match_exprstates _ _ _ _ _ _ _ _ _ _ _ _ unit linked
        functionMatch (expressionMatch value memory) expressionContMatch⟩
      apply plus_one
      exact Clight.step_returnstate _ _ _ _ _ _ _

end
end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem simulation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    simulationStatement := by
  intro external source target programs before events after stepped translated matched
  rcases stepped with expressionStep | statementStep
  · exact estep_simulation external source target programs _ _ _ expressionStep _ matched
  · exact sstep_simulation external source target programs _ _ _ statementStep _ matched

end CompCert4Lean.Cfrontend.SimplExprproof

namespace CompCert4Lean.Cfrontend.SimplExprproof

theorem transl_program_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transl_program_correctStatement := by
  intro external source target programs
  exact CompCert4Lean.Common.Smallstep.forward_simulation_star_wf
    (Cstrategy.semantics external source) (Clight.semantics1 external target)
    (senv_preserved source target programs).2.1
    (match_states source target) (transl_initial_states source target programs)
    (transl_final_states source target) (fun next previous => measure next < measure previous)
    (InvImage.wf measure Nat.lt_wfRel.wf) (simulation external source target programs)

end CompCert4Lean.Cfrontend.SimplExprproof
