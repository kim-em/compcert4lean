import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Linking
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Cfrontend.SimplLocals
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.FSetFacts
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps

/-!
# Semantic preservation surface for SimplLocals

Definition-bearing translation of CompCert's `cfrontend/SimplLocalsproof.v`.
The simulation relations and executable predicates are present now; proof
bodies scheduled for the later proof-migration phase are represented by exact
proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev memory_chunk := CompCert4Lean.Common.AST.memory_chunk
private abbrev program := CompCert4Lean.Cfrontend.Clight.program
private abbrev function := CompCert4Lean.Cfrontend.Clight.function
private abbrev fundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev genv := CompCert4Lean.Cfrontend.Clight.genv
private abbrev env := CompCert4Lean.Cfrontend.Clight.env
private abbrev temp_env := CompCert4Lean.Cfrontend.Clight.temp_env
private abbrev expr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev statement := CompCert4Lean.Cfrontend.Clight.statement
private abbrev labeled_statements := CompCert4Lean.Cfrontend.Clight.labeled_statements
private abbrev cont := CompCert4Lean.Cfrontend.Clight.cont
private abbrev state := CompCert4Lean.Cfrontend.Clight.machine_state
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev compilenv := CompCert4Lean.Cfrontend.SimplLocals.compilenv
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

/-! ## Generated finite-set facts surface -/

namespace VSF

private abbrev F := CompCert4Lean.Cfrontend.SimplLocals.VSet.MFProvider

abbrev add_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.add_iff F
abbrev empty_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.empty_iff F
abbrev mem_iff := CompCert4Lean.Lib.FSetFacts.WFacts_fun.mem_iff F

end VSF

def match_prog (cfg : CompilerConfig) (p tp : program) : Prop :=
  @match_program
    (CompCert4Lean.Cfrontend.Ctypes.fundef function) type
    (CompCert4Lean.Cfrontend.Ctypes.fundef function) type
    (CompCert4Lean.Cfrontend.Ctypes.Linker_fundef function)
    CompCert4Lean.Cfrontend.Ctypes.Linker_types
    (fun _ f tf => transf_fundef cfg f = .OK tf) Eq
    (program_of_program p) (program_of_program tp) ∧
    tp.prog_types = p.prog_types

inductive match_var (f : meminj) (cenv : compilenv) (e : env) (m : mem)
    (te : env) (tle : temp_env) (id : ident) : Prop where
  | match_var_lifted (b : block) (ty : type) (chunk : memory_chunk)
      (v tv : val)
      (ENV : PTree.get id e = some (b, ty))
      (TENV : PTree.get id te = none)
      (LIFTED : VSet.mem id cenv = true)
      (MAPPED : f b = none)
      (MODE : access_mode ty = .By_value chunk)
      (LOAD : Mem.load chunk m b .Z0 = some v)
      (TLENV : PTree.get id tle = some tv)
      (VINJ : Val.inject f v tv) :
      match_var f cenv e m te tle id
  | match_var_not_lifted (b : block) (ty : type) (b' : block)
      (ENV : PTree.get id e = some (b, ty))
      (TENV : PTree.get id te = some (b', ty))
      (LIFTED : VSet.mem id cenv = false)
      (MAPPED : f b = some (b', .Z0)) :
      match_var f cenv e m te tle id
  | match_var_not_local
      (ENV : PTree.get id e = none)
      (TENV : PTree.get id te = none)
      (LIFTED : VSet.mem id cenv = false) :
      match_var f cenv e m te tle id

export match_var (match_var_lifted match_var_not_lifted match_var_not_local)

structure match_envs (f : meminj) (cenv : compilenv)
    (e : env) (le : temp_env) (m : mem) (lo hi : block)
    (te : env) (tle : temp_env) (tlo thi : block) : Prop where
  me_vars : ∀ id, match_var f cenv e m te tle id
  me_temps : ∀ id v, PTree.get id le = some v →
    (∃ tv, PTree.get id tle = some tv ∧ Val.inject f v tv) ∧
    (VSet.mem id cenv = true → v = .Vundef)
  me_inj : ∀ id1 b1 ty1 id2 b2 ty2,
    PTree.get id1 e = some (b1, ty1) →
    PTree.get id2 e = some (b2, ty2) → id1 ≠ id2 → b1 ≠ b2
  me_range : ∀ id b ty, PTree.get id e = some (b, ty) → Ple lo b ∧ Plt b hi
  me_trange : ∀ id b ty, PTree.get id te = some (b, ty) → Ple tlo b ∧ Plt b thi
  me_mapped : ∀ id b' ty, PTree.get id te = some (b', ty) →
    ∃ b, f b = some (b', .Z0) ∧ PTree.get id e = some (b, ty)
  me_flat : ∀ id b' ty b delta,
    PTree.get id te = some (b', ty) → f b = some (b', delta) →
    PTree.get id e = some (b, ty) ∧ delta = .Z0
  me_incr : Ple lo hi
  me_tincr : Ple tlo thi

export match_envs (me_vars me_temps me_inj me_range me_trange me_mapped
  me_flat me_incr me_tincr)

abbrev mk_match_envs := @match_envs.mk

inductive val_casted_list : List val → List type → Prop where
  | nil : val_casted_list [] []
  | cons (v : val) (vl : List val) (ty : type) (tyl : List type) :
      val_casted v ty → val_casted_list vl tyl →
      val_casted_list (v :: vl) (ty :: tyl)

abbrev vcl_nil := @val_casted_list.nil
abbrev vcl_cons := @val_casted_list.cons

def cenv_for_gen (atk : VSet.t) (vars : List (ident × type)) : compilenv :=
  vars.foldr (add_local_variable atk) VSet.empty

def compat_cenv (atk : VSet.t) (cenv : compilenv) : Prop :=
  ∀ id, VSet.In id atk → VSet.In id cenv → False

def env_initial_value (e : env) (m : mem) : Prop :=
  ∀ id b ty chunk,
    PTree.get id e = some (b, ty) →
    access_mode ty = .By_value chunk →
    Mem.load chunk m b .Z0 = some .Vundef

def freelist_no_overlap : List (block × Z × Z) → Prop
  | [] => True
  | (b, lo, hi) :: rest =>
      freelist_no_overlap rest ∧
      ∀ b' lo' hi', (b', lo', hi') ∈ rest →
        b' ≠ b ∨ ZArith.BinInt.Z.le hi' lo ∨ ZArith.BinInt.Z.le hi lo'

inductive match_globalenvs (prog : program) (f : meminj) (bound : block) : Prop where
  | intro
      (DOMAIN : ∀ b, Plt b bound → f b = some (b, .Z0))
      (IMAGE : ∀ b1 b2 delta,
        f b1 = some (b2, delta) → Plt b2 bound → b1 = b2)
      (SYMBOLS : ∀ id b,
        Genv.find_symbol (Genv.globalenv (program_of_program prog)) id = some b → Plt b bound)
      (FUNCTIONS : ∀ b fd,
        Genv.find_funct_ptr (Genv.globalenv (program_of_program prog)) b = some fd → Plt b bound)
      (VARINFOS : ∀ b gv,
        Genv.find_var_info (Genv.globalenv (program_of_program prog)) b = some gv → Plt b bound) :
      match_globalenvs prog f bound

abbrev mk_match_globalenvs := @match_globalenvs.intro

inductive match_cont (cfg : CompilerConfig) (prog : program) (f : meminj) :
    compilenv → cont → cont → mem → block → block → Prop where
  | stop (cenv : compilenv) (m : mem) (bound tbound hi : block) :
      match_globalenvs prog f hi → Ple hi bound → Ple hi tbound →
      match_cont cfg prog f cenv .Kstop .Kstop m bound tbound
  | seq (cenv : compilenv) (s : statement) (k : cont)
      (ts : statement) (tk : cont) (m : mem) (bound tbound : block) :
      simpl_stmt cfg cenv s = .OK ts →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_stmt s) cenv →
      match_cont cfg prog f cenv (.Kseq s k) (.Kseq ts tk) m bound tbound
  | loop1 (cenv : compilenv) (s1 s2 : statement) (k : cont)
      (ts1 ts2 : statement) (tk : cont) (m : mem) (bound tbound : block) :
      simpl_stmt cfg cenv s1 = .OK ts1 → simpl_stmt cfg cenv s2 = .OK ts2 →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv →
      match_cont cfg prog f cenv (.Kloop1 s1 s2 k) (.Kloop1 ts1 ts2 tk) m bound tbound
  | loop2 (cenv : compilenv) (s1 s2 : statement) (k : cont)
      (ts1 ts2 : statement) (tk : cont) (m : mem) (bound tbound : block) :
      simpl_stmt cfg cenv s1 = .OK ts1 → simpl_stmt cfg cenv s2 = .OK ts2 →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv →
      match_cont cfg prog f cenv (.Kloop2 s1 s2 k) (.Kloop2 ts1 ts2 tk) m bound tbound
  | switch (cenv : compilenv) (k tk : cont) (m : mem) (bound tbound : block) :
      match_cont cfg prog f cenv k tk m bound tbound →
      match_cont cfg prog f cenv (.Kswitch k) (.Kswitch tk) m bound tbound
  | match_Kcall (cenv : compilenv) (optid : Option ident) (fn : function)
      (e : env) (le : temp_env) (k : cont) (tfn : function)
      (te : env) (tle : temp_env) (tk : cont) (m : mem)
      (hi thi lo tlo bound tbound : block) (x : Unit) :
      transf_function cfg fn = .OK tfn →
      match_envs f (cenv_for fn) e le m lo hi te tle tlo thi →
      match_cont cfg prog f (cenv_for fn) k tk m lo tlo →
      check_opttemp (cenv_for fn) optid = .OK x →
      Ple hi bound → Ple thi tbound →
      match_cont cfg prog f cenv (.Kcall optid fn e le k)
        (.Kcall optid tfn te tle tk) m bound tbound

abbrev match_Kstop := @match_cont.stop
abbrev match_Kseq := @match_cont.seq
abbrev match_Kloop1 := @match_cont.loop1
abbrev match_Kloop2 := @match_cont.loop2
abbrev match_Kswitch := @match_cont.switch
export match_cont (match_Kcall)

inductive match_states (cfg : CompilerConfig) (prog : program) : state → state → Prop where
  | regular (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) (tf : function) (ts : statement)
      (tk : cont) (te : env) (tle : temp_env) (tm : mem)
      (j : meminj) (lo hi tlo thi : block) :
      transf_function cfg f = .OK tf →
      simpl_stmt cfg (cenv_for f) s = .OK ts →
      match_envs j (cenv_for f) e le m lo hi te tle tlo thi →
      match_cont cfg prog j (cenv_for f) k tk m lo tlo →
      Mem.inject j m tm →
      compat_cenv (addr_taken_stmt s) (cenv_for f) →
      Ple hi m.nextblock → Ple thi tm.nextblock →
      match_states cfg prog (.State f s k e le m) (.State tf ts tk te tle tm)
  | call (fd : fundef) (vargs : List val) (k : cont) (m : mem)
      (tfd : fundef) (tvargs : List val) (tk : cont) (tm : mem)
      (j : meminj) (targs : List type) (tres : type) (cconv : calling_convention) :
      transf_fundef cfg fd = .OK tfd →
      (∀ cenv, match_cont cfg prog j cenv k tk m m.nextblock tm.nextblock) →
      Mem.inject j m tm → Val.inject_list j vargs tvargs →
      type_of_fundef fd = .Tfunction targs tres cconv →
      val_casted_list vargs targs →
      match_states cfg prog (.Callstate fd vargs k m) (.Callstate tfd tvargs tk tm)
  | return_ (v : val) (k : cont) (m : mem) (tv : val) (tk : cont)
      (tm : mem) (j : meminj) :
      (∀ cenv, match_cont cfg prog j cenv k tk m m.nextblock tm.nextblock) →
      Mem.inject j m tm → Val.inject j v tv →
      match_states cfg prog (.Returnstate v k m) (.Returnstate tv tk tm)

abbrev match_regular_states := @match_states.regular
abbrev match_call_state := @match_states.call
abbrev match_return_state := @match_states.return_

/-! ## Exact statement descriptors for later proof migration -/

def match_transf_programStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program),
    transf_program cfg p = .OK tp → match_prog cfg p tp

def comp_env_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    (globalenv tp).genv_cenv = (globalenv p).genv_cenv

def symbols_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ id, Genv.find_symbol (globalenv tp).genv_genv id =
      Genv.find_symbol (globalenv p).genv_genv id

def senv_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    Senv.equiv (Genv.to_senv (globalenv p).genv_genv)
      (Genv.to_senv (globalenv tp).genv_genv)

def function_ptr_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ b fd, Genv.find_funct_ptr (globalenv p).genv_genv b = some fd →
      ∃ tfd, Genv.find_funct_ptr (globalenv tp).genv_genv b = some tfd ∧
        transf_fundef cfg fd = .OK tfd

def type_of_fundef_preservedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (fd tfd : fundef),
    transf_fundef cfg fd = .OK tfd → type_of_fundef tfd = type_of_fundef fd

def match_envs_invariantStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi f' m',
    match_envs f cenv e le m lo hi te tle tlo thi →
    (∀ b chunk v, f b = none → Ple lo b ∧ Plt b hi →
      Mem.load chunk m b (.Z0 : Z) = some v →
      Mem.load chunk m' b (.Z0 : Z) = some v) →
    inject_incr f f' →
    (∀ b, Ple lo b ∧ Plt b hi → f' b = f b) →
    (∀ b b' delta, f' b = some (b', delta) →
      Ple tlo b' ∧ Plt b' thi → f' b = f b) →
    match_envs f' cenv e le m' lo hi te tle tlo thi

def match_envs_extcallStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi tm f' m',
    match_envs f cenv e le m lo hi te tle tlo thi →
    Mem.unchanged_on (loc_unmapped f) m m' →
    inject_incr f f' → inject_separated f f' m tm →
    Ple hi m.nextblock → Ple thi tm.nextblock →
    match_envs f' cenv e le m' lo hi te tle tlo thi

def val_casted_load_resultStatement : Prop :=
  ∀ v ty chunk, val_casted v ty → access_mode ty = .By_value chunk →
    Val.load_result chunk v = v

def val_casted_injectStatement : Prop :=
  ∀ f v v' ty, Val.inject f v v' → val_casted v ty → val_casted v' ty

def forall2_val_casted_injectStatement : Prop :=
  ∀ f vl vl', Val.inject_list f vl vl' →
    ∀ tyl, CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl tyl →
      CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl' tyl

def val_casted_list_paramsStatement : Prop :=
  ∀ params vl, val_casted_list vl (type_of_params params) →
    CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl (params.map Prod.snd)

def make_cast_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (tprog : program) e le m a v1 tto v2,
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) (globalenv tprog) e le m a v1 →
    sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 (typeof a) tto m = some v2 →
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) (globalenv tprog) e le m
        (make_cast a tto) v2

def cast_typeconvStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty m, val_casted v ty →
    sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v ty (typeconv ty) m = some v

def step_Sdebug_tempStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : program) f id ty k e le m v,
    PTree.get id le = some v → val_casted v ty →
    step2
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (globalenv tprog)
      (.State f (Sdebug_temp id ty) k e le m) E0
      (.State f .Sskip k e le m)

def step_Sdebug_varStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (xi : ExternalCalls) (tprog : program) f id ty k e le m b,
    PTree.get id e = some (b, ty) →
    step2
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi (globalenv tprog)
      (.State f (Sdebug_var id ty) k e le m) E0
      (.State f .Sskip k e le m)

def step_Sset_debugStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program)
    f id ty a k e le m v v',
    eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) (globalenv tprog) e le m a v →
    sem_cast
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v (typeof a) ty m = some v' →
    plus
      (step2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
      (globalenv tprog) (.State f (Sset_debug cfg id ty a) k e le m) E0
      (.State f .Sskip k e (PTree.set id v' le) m)

def step_add_debug_varsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program)
    f s e le m vars k,
    (∀ id ty, (id, ty) ∈ vars → ∃ b, PTree.get id e = some (b, ty)) →
    star
      (step2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
      (globalenv tprog) (.State f (add_debug_vars cfg vars s) k e le m) E0
      (.State f s k e le m)

def bind_parameter_temps_invStatement : Prop :=
  ∀ id params args le le',
    bind_parameter_temps params args le = some le' →
    id ∉ var_names params → PTree.get id le' = PTree.get id le

def step_add_debug_paramsStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (tprog : program)
    f s k e le m params vl le1,
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params) →
    CompCert4Lean.Lib.Coqlib.list_forall2 val_casted vl (params.map Prod.snd) →
    bind_parameter_temps params vl le1 = some le →
    star
      (step2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi)
      (globalenv tprog) (.State f (add_debug_params cfg params s) k e le m) E0
      (.State f s k e le m)

def match_envs_assign_liftedStatement : Prop :=
  ∀ (prog : program) f cenv e le m lo hi te tle tlo thi b ty v m' id tv,
    match_envs f cenv e le m lo hi te tle tlo thi →
    PTree.get id e = some (b, ty) → val_casted v ty → Val.inject f v tv →
    assign_loc (globalenv prog).genv_cenv ty m b Ptrofs.zero .Full v m' →
    VSet.mem id cenv = true →
    match_envs f cenv e le m' lo hi te (PTree.set id tv tle) tlo thi

def match_envs_set_tempStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi id v tv x,
    match_envs f cenv e le m lo hi te tle tlo thi → Val.inject f v tv →
    check_temp cenv id = .OK x →
    match_envs f cenv e (PTree.set id v le) m lo hi te
      (PTree.set id tv tle) tlo thi

def match_envs_set_opttempStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi optid v tv x,
    match_envs f cenv e le m lo hi te tle tlo thi → Val.inject f v tv →
    check_opttemp cenv optid = .OK x →
    match_envs f cenv e (set_opttemp optid v le) m lo hi te
      (set_opttemp optid tv tle) tlo thi

def match_envs_temps_extenStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi tle',
    match_envs f cenv e le m lo hi te tle tlo thi →
    (∀ id, PTree.get id tle' = PTree.get id tle) →
    match_envs f cenv e le m lo hi te tle' tlo thi

def match_envs_change_tempStatement : Prop :=
  ∀ f cenv e le m lo hi te tle tlo thi id v,
    match_envs f cenv e le m lo hi te tle tlo thi →
    PTree.get id le = none → VSet.mem id cenv = false →
    match_envs f cenv e le m lo hi te (PTree.set id v tle) tlo thi

def add_local_variable_charactStatement : Prop :=
  ∀ id ty atk cenv id1,
    VSet.In id1 (add_local_variable atk (id, ty) cenv) ↔
      VSet.In id1 cenv ∨
        ∃ chunk, access_mode ty = .By_value chunk ∧ id = id1 ∧
          VSet.mem id atk = false

def cenv_for_gen_domainStatement : Prop :=
  ∀ atk id vars, VSet.In id (cenv_for_gen atk vars) → id ∈ var_names vars

def cenv_for_gen_by_valueStatement : Prop :=
  ∀ atk id ty vars, (id, ty) ∈ vars →
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names vars) →
    VSet.In id (cenv_for_gen atk vars) →
    ∃ chunk, access_mode ty = .By_value chunk

def cenv_for_gen_compatStatement : Prop :=
  ∀ atk id vars, VSet.In id (cenv_for_gen atk vars) → VSet.mem id atk = false

def compat_cenv_forStatement : Prop :=
  ∀ f, compat_cenv (addr_taken_stmt f.fn_body) (cenv_for f)

def compat_cenv_union_lStatement : Prop :=
  ∀ atk1 atk2 cenv,
    compat_cenv (VSet.union atk1 atk2) cenv → compat_cenv atk1 cenv

def compat_cenv_union_rStatement : Prop :=
  ∀ atk1 atk2 cenv,
    compat_cenv (VSet.union atk1 atk2) cenv → compat_cenv atk2 cenv

def compat_cenv_emptyStatement : Prop :=
  ∀ cenv, compat_cenv VSet.empty cenv

def alloc_variables_nextblockStatement : Prop :=
  ∀ ge e m vars e' m', alloc_variables ge e m vars e' m' →
    Ple m.nextblock m'.nextblock

def alloc_variables_rangeStatement : Prop :=
  ∀ ge id b ty e m vars e' m', alloc_variables ge e m vars e' m' →
    PTree.get id e' = some (b, ty) →
    PTree.get id e = some (b, ty) ∨ Ple m.nextblock b ∧ Plt b m'.nextblock

def alloc_variables_injectiveStatement : Prop :=
  ∀ ge id1 b1 ty1 id2 b2 ty2 e m vars e' m',
    alloc_variables ge e m vars e' m' →
    (PTree.get id1 e = some (b1, ty1) → PTree.get id2 e = some (b2, ty2) →
      id1 ≠ id2 → b1 ≠ b2) →
    (∀ id b ty, PTree.get id e = some (b, ty) → Plt b m.nextblock) →
    PTree.get id1 e' = some (b1, ty1) → PTree.get id2 e' = some (b2, ty2) →
    id1 ≠ id2 → b1 ≠ b2

def match_alloc_variablesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ cenv e m vars e' m', alloc_variables ge e m vars e' m' →
    ∀ j tm te, CompCert4Lean.Lib.Coqlib.list_norepet (var_names vars) →
    Mem.inject j m tm →
    ∃ j' te' tm',
      alloc_variables tge te tm (remove_lifted cenv vars) te' tm' ∧
      Mem.inject j' m' tm' ∧ inject_incr j j' ∧
      (∀ b, Mem.valid_block m b → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) →
        Mem.valid_block tm b' → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) → ¬ Mem.valid_block tm b' →
        ∃ id ty, PTree.get id e' = some (b, ty) ∧
          PTree.get id te' = some (b', ty) ∧ delta = (.Z0 : Z)) ∧
      (∀ id ty, (id, ty) ∈ vars → ∃ b,
        PTree.get id e' = some (b, ty) ∧
        if VSet.mem id cenv then PTree.get id te' = PTree.get id te ∧ j' b = none
        else ∃ tb, PTree.get id te' = some (tb, ty) ∧ j' b = some (tb, (.Z0 : Z))) ∧
      (∀ id, id ∉ var_names vars →
        PTree.get id e' = PTree.get id e ∧ PTree.get id te' = PTree.get id te)

def alloc_variables_loadStatement : Prop :=
  ∀ (prog : program) e m vars e' m',
    alloc_variables (globalenv prog) e m vars e' m' →
    ∀ chunk b ofs v, Mem.load chunk m b ofs = some v →
      Mem.load chunk m' b ofs = some v

def sizeof_by_valueStatement : Prop :=
  ∀ (prog : program) ty chunk, access_mode ty = .By_value chunk →
    ZArith.BinInt.Z.le (CompCert4Lean.Common.Memdata.size_chunk chunk)
      (sizeof (globalenv prog).genv_cenv ty)

def alloc_variables_initial_valueStatement : Prop :=
  ∀ (prog : program) e m vars e' m',
    alloc_variables (globalenv prog) e m vars e' m' →
    env_initial_value e m → env_initial_value e' m'

def create_undef_temps_charactStatement : Prop :=
  ∀ id ty vars, (id, ty) ∈ vars → PTree.get id (create_undef_temps vars) = some .Vundef

def create_undef_temps_invStatement : Prop :=
  ∀ vars id v, PTree.get id (create_undef_temps vars) = some v →
    v = .Vundef ∧ id ∈ var_names vars

def create_undef_temps_extenStatement : Prop :=
  ∀ id l1 l2, (id ∈ var_names l1 ↔ id ∈ var_names l2) →
    PTree.get id (create_undef_temps l1) = PTree.get id (create_undef_temps l2)

def var_names_appStatement : Prop :=
  ∀ vars1 vars2, var_names (vars1 ++ vars2) = var_names vars1 ++ var_names vars2

def filter_appStatement : Prop :=
  ∀ (A : Type) (f : A → Bool) l1 l2,
    List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2

def filter_charactStatement : Prop :=
  ∀ (A : Type) (f : A → Bool) x l,
    x ∈ List.filter f l ↔ x ∈ l ∧ f x = true

def filter_norepetStatement : Prop :=
  ∀ (A : Type) (f : A → Bool) l,
    CompCert4Lean.Lib.Coqlib.list_norepet l →
    CompCert4Lean.Lib.Coqlib.list_norepet (List.filter f l)

def filter_mapStatement : Prop :=
  ∀ (A B : Type) (f : A → B) (pa : A → Bool) (pb : B → Bool),
    (∀ a, pb (f a) = pa a) → ∀ l,
      List.map f (List.filter pa l) = List.filter pb (List.map f l)

def create_undef_temps_liftedStatement : Prop :=
  ∀ id f, id ∉ var_names f.fn_params →
    PTree.get id (create_undef_temps (add_lifted (cenv_for f) f.fn_vars f.fn_temps)) =
    PTree.get id (create_undef_temps
      (add_lifted (cenv_for f) (f.fn_params ++ f.fn_vars) f.fn_temps))

def vars_and_temps_propertiesStatement : Prop :=
  ∀ cenv params vars temps,
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params ++ var_names vars) →
    list_disjoint (var_names params) (var_names temps) →
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params) ∧
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names (remove_lifted cenv (params ++ vars))) ∧
    list_disjoint (var_names params) (var_names (add_lifted cenv vars temps))

def match_envs_alloc_variablesStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ cenv m vars e m' temps j tm,
    alloc_variables ge empty_env m vars e m' →
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names vars) →
    Mem.inject j m tm →
    (∀ id ty, (id, ty) ∈ vars → VSet.mem id cenv = true →
      ∃ chunk, access_mode ty = .By_value chunk) →
    (∀ id, VSet.mem id cenv = true → id ∈ var_names vars) →
    ∃ j' te tm',
      alloc_variables tge empty_env tm (remove_lifted cenv vars) te tm' ∧
      match_envs j' cenv e (create_undef_temps temps) m'
        m.nextblock m'.nextblock te
        (create_undef_temps (add_lifted cenv vars temps)) tm.nextblock tm'.nextblock ∧
      Mem.inject j' m' tm' ∧ inject_incr j j' ∧
      (∀ b, Mem.valid_block m b → j' b = j b) ∧
      (∀ b b' delta, j' b = some (b', delta) →
        Mem.valid_block tm b' → j' b = j b) ∧
      (∀ id ty, (id, ty) ∈ vars → VSet.mem id cenv = false →
        ∃ b, PTree.get id te = some (b, ty))

def assign_loc_injectStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ f ty m loc ofs bf v m' tm loc' ofs' v',
    assign_loc ge.genv_cenv ty m loc ofs bf v m' →
    Val.inject f (.Vptr loc ofs) (.Vptr loc' ofs') → Val.inject f v v' →
    Mem.inject f m tm →
    ∃ tm', assign_loc tge.genv_cenv ty tm loc' ofs' bf v' tm' ∧
      Mem.inject f m' tm' ∧
      ∀ b chunk value, f b = none →
        Mem.load chunk m b (.Z0 : Z) = some value →
        Mem.load chunk m' b (.Z0 : Z) = some value

def assign_loc_nextblockStatement : Prop :=
  ∀ ge ty m b ofs bf v m', assign_loc ge ty m b ofs bf v m' →
    m'.nextblock = m.nextblock

def store_params_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p tp : program),
    match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ j f k cenv le lo hi te tlo thi e m params args m',
    bind_parameters ge e m params args m' →
    ∀ s tm tle1 tle2 targs,
    CompCert4Lean.Lib.Coqlib.list_norepet (var_names params) →
    CompCert4Lean.Lib.Coqlib.list_forall2 val_casted args (params.map Prod.snd) →
    Val.inject_list j args targs →
    match_envs j cenv e le m lo hi te tle1 tlo thi → Mem.inject j m tm →
    (∀ id, id ∉ var_names params → PTree.get id tle2 = PTree.get id tle1) →
    (∀ id, id ∈ var_names params → PTree.get id le = none) →
    ∃ tle tm',
      star
        (step2
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) xi)
        tge (.State f (store_params cenv params s) k te tle tm) E0
        (.State f s k te tle tm') ∧
      bind_parameter_temps params targs tle2 = some tle ∧
      Mem.inject j m' tm' ∧ match_envs j cenv e le m' lo hi te tle tlo thi ∧
      tm'.nextblock = tm.nextblock

def bind_parameters_nextblockStatement : Prop :=
  ∀ ge e m params args m', bind_parameters ge e m params args m' →
    m'.nextblock = m.nextblock

def bind_parameters_loadStatement : Prop :=
  ∀ ge e chunk b ofs,
    (∀ id b' ty, PTree.get id e = some (b', ty) → b ≠ b') →
    ∀ m params args m', bind_parameters ge e m params args m' →
      Mem.load chunk m' b ofs = Mem.load chunk m b ofs

def free_blocks_of_env_perm_1Statement : Prop :=
  ∀ ce m e m' id b ty ofs k permission,
    Mem.free_list m (blocks_of_env ce e) = some m' →
    PTree.get id e = some (b, ty) → Mem.perm m' b ofs k permission →
    ZArith.BinInt.Z.le (.Z0 : Z) ofs ∧
      ZArith.BinInt.Z.lt ofs (sizeof ce.genv_cenv ty) → False

def free_list_perm'Statement : Prop :=
  ∀ b lo hi l m m', Mem.free_list m l = some m' → (b, lo, hi) ∈ l →
    Mem.range_perm m b lo hi .Cur .Freeable

def free_blocks_of_env_perm_2Statement : Prop :=
  ∀ ce m e m' id b ty, Mem.free_list m (blocks_of_env ce e) = some m' →
    PTree.get id e = some (b, ty) →
    Mem.range_perm m b (.Z0 : Z) (sizeof ce.genv_cenv ty) .Cur .Freeable

def can_free_listStatement : Prop :=
  ∀ l m,
    (∀ b lo hi, (b, lo, hi) ∈ l → Mem.range_perm m b lo hi .Cur .Freeable) →
    freelist_no_overlap l → ∃ m', Mem.free_list m l = some m'

def blocks_of_env_no_overlapStatement : Prop :=
  ∀ (ge : genv) j cenv e le m lo hi te tle tlo thi tm,
    match_envs j cenv e le m lo hi te tle tlo thi → Mem.inject j m tm →
    (∀ id b ty, PTree.get id e = some (b, ty) →
      Mem.range_perm m b (.Z0 : Z) (sizeof ge.genv_cenv ty) .Cur .Freeable) →
    ∀ (l : List (ident × (block × type))),
    CompCert4Lean.Lib.Coqlib.list_norepet (l.map Prod.fst) →
    (∀ id bty, (id, bty) ∈ l → PTree.get id te = some bty) →
    freelist_no_overlap (l.map (block_of_binding ge))

def free_list_right_injectStatement : Prop :=
  ∀ j m1 l m2 m2', Mem.inject j m1 m2 → Mem.free_list m2 l = some m2' →
    (∀ b1 b2 delta lo hi ofs k permission,
      j b1 = some (b2, delta) → (b2, lo, hi) ∈ l →
      Mem.perm m1 b1 ofs k permission →
      ZArith.BinInt.Z.le lo (ZArith.BinInt.Z.add ofs delta) ∧
        ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) hi → False) →
    Mem.inject j m1 m2'

def blocks_of_env_translatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ e, blocks_of_env (globalenv tp) e = blocks_of_env (globalenv p) e

def match_envs_free_blocksStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ j cenv e le m lo hi te tle tlo thi m' tm,
    match_envs j cenv e le m lo hi te tle tlo thi → Mem.inject j m tm →
    Mem.free_list m (blocks_of_env ge e) = some m' →
    ∃ tm', Mem.free_list tm (blocks_of_env tge te) = some tm' ∧ Mem.inject j m' tm'

def match_globalenvs_preserves_globalsStatement : Prop :=
  ∀ (prog : program) f, (∃ bound, match_globalenvs prog f bound) →
    meminj_preserves_globals fundef type (Genv.globalenv (program_of_program prog)) f

def typeof_simpl_exprStatement : Prop :=
  ∀ cenv a, typeof (simpl_expr cenv a) = typeof a

def deref_loc_injectStatement : Prop :=
  ∀ m tm f, Mem.inject f m tm →
    ∀ ty loc ofs bf v loc' ofs', deref_loc ty m loc ofs bf v →
    Val.inject f (.Vptr loc ofs) (.Vptr loc' ofs') →
    ∃ tv, deref_loc ty tm loc' ofs' bf tv ∧ Val.inject f v tv

def eval_simpl_exprStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ e te le tle m tm f cenv lo hi tlo thi,
    match_envs f cenv e le m lo hi te tle tlo thi → Mem.inject f m tm →
    (∃ bound, match_globalenvs p f bound) →
    ∀ a v,
      eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v →
      compat_cenv (addr_taken_expr a) cenv →
      ∃ tv,
        eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) tge te tle tm
            (simpl_expr cenv a) tv ∧ Val.inject f v tv

def eval_simpl_lvalueStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ e te le tle m tm f cenv lo hi tlo thi,
    match_envs f cenv e le m lo hi te tle tlo thi → Mem.inject f m tm →
    (∃ bound, match_globalenvs p f bound) →
    ∀ a b ofs bf,
      eval_lvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a b ofs bf →
    compat_cenv (addr_taken_expr a) cenv →
    (match a with | .Evar id _ => VSet.mem id cenv = false | _ => True) →
    ∃ b' ofs',
      eval_lvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) tge te tle tm
          (simpl_expr cenv a) b' ofs' bf ∧
      Val.inject f (.Vptr b ofs) (.Vptr b' ofs')

def eval_simpl_exprlistStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ e te le tle m tm f cenv lo hi tlo thi,
    match_envs f cenv e le m lo hi te tle tlo thi → Mem.inject f m tm →
    (∃ bound, match_globalenvs p f bound) →
    ∀ al tyl vl,
      eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m al tyl vl →
    compat_cenv (addr_taken_exprlist al) cenv →
    val_casted_list vl tyl ∧
      ∃ tvl,
        eval_exprlist
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) tge te tle tm
            (simpl_exprlist cenv al) tyl tvl ∧
        Val.inject_list f vl tvl

def match_cont_invariantStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f' m' f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound →
    (∀ b chunk v, f b = none → Plt b bound →
      Mem.load chunk m b (.Z0 : Z) = some v →
      Mem.load chunk m' b (.Z0 : Z) = some v) →
    inject_incr f f' →
    (∀ b, Plt b bound → f' b = f b) →
    (∀ b b' delta, f' b = some (b', delta) → Plt b' tbound → f' b = f b) →
    match_cont cfg prog f' cenv k tk m' bound tbound

def match_cont_assign_locStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound ty loc ofs bf v m',
    match_cont cfg prog f cenv k tk m bound tbound →
    assign_loc (globalenv prog).genv_cenv ty m loc ofs bf v m' → Ple bound loc →
    match_cont cfg prog f cenv k tk m' bound tbound

def match_cont_extcallStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound tm f' m',
    match_cont cfg prog f cenv k tk m bound tbound →
    Mem.unchanged_on (loc_unmapped f) m m' → inject_incr f f' →
    inject_separated f f' m tm → Ple bound m.nextblock → Ple tbound tm.nextblock →
    match_cont cfg prog f' cenv k tk m' bound tbound

def match_cont_incr_boundsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound →
    ∀ bound' tbound', Ple bound bound' → Ple tbound tbound' →
      match_cont cfg prog f cenv k tk m bound' tbound'

def match_cont_change_cenvStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound cenv',
    match_cont cfg prog f cenv k tk m bound tbound → is_call_cont k →
    match_cont cfg prog f cenv' k tk m bound tbound

def match_cont_is_call_contStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound → is_call_cont k → is_call_cont tk

def match_cont_call_contStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound → ∀ cenv',
    match_cont cfg prog f cenv' (call_cont k) (call_cont tk) m bound tbound

def free_list_nextblockStatement : Prop :=
  ∀ l m m', Mem.free_list m l = some m' → m'.nextblock = m.nextblock

def free_list_loadStatement : Prop :=
  ∀ chunk b' l m m', Mem.free_list m l = some m' →
    (∀ b lo hi, (b, lo, hi) ∈ l → Plt b' b) →
    Mem.load chunk m' b' (.Z0 : Z) = Mem.load chunk m b' (.Z0 : Z)

def match_cont_free_envStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog tprog : program),
    let ge := globalenv prog
    let tge := globalenv tprog
    ∀ f cenv e le m lo hi te tle tm tlo thi k tk m' tm',
    match_envs f cenv e le m lo hi te tle tlo thi →
    match_cont cfg prog f cenv k tk m lo tlo → Ple hi m.nextblock →
    Ple thi tm.nextblock → Mem.free_list m (blocks_of_env ge e) = some m' →
    Mem.free_list tm (blocks_of_env tge te) = some tm' →
    match_cont cfg prog f cenv k tk m' m'.nextblock tm'.nextblock

def match_cont_globalenvStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv k tk m bound tbound,
    match_cont cfg prog f cenv k tk m bound tbound →
    ∃ bound, match_globalenvs prog f bound

def match_cont_find_functStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ f cenv k tk m bound tbound vf fd tvf,
    match_cont cfg p f cenv k tk m bound tbound →
    Genv.find_funct (Genv.globalenv (program_of_program p)) vf = some fd → Val.inject f vf tvf →
    ∃ tfd, Genv.find_funct (Genv.globalenv (program_of_program tp)) tvf = some tfd ∧
      transf_fundef cfg fd = .OK tfd

def is_liftable_var_charactStatement : Prop :=
  ∀ cenv a,
    match is_liftable_var cenv a with
    | some id => ∃ ty, a = .Evar id ty ∧ VSet.mem id cenv = true
    | none => match a with | .Evar id _ => VSet.mem id cenv = false | _ => True

def simpl_select_switchStatement : Prop :=
  ∀ cfg cenv n ls tls, simpl_lblstmt cfg cenv ls = .OK tls →
    simpl_lblstmt cfg cenv (select_switch n ls) = .OK (select_switch n tls)

def simpl_seq_of_labeled_statementStatement : Prop :=
  ∀ cfg cenv ls tls, simpl_lblstmt cfg cenv ls = .OK tls →
    simpl_stmt cfg cenv (seq_of_labeled_statement ls) =
      .OK (seq_of_labeled_statement tls)

def compat_cenv_select_switchStatement : Prop :=
  ∀ cenv n ls, compat_cenv (addr_taken_lblstmt ls) cenv →
    compat_cenv (addr_taken_lblstmt (select_switch n ls)) cenv

def addr_taken_seq_of_labeled_statementStatement : Prop :=
  ∀ ls, addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls

def simpl_find_labelStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv m bound tbound lbl s k ts tk,
    simpl_stmt cfg cenv s = .OK ts →
    match_cont cfg prog f cenv k tk m bound tbound →
    compat_cenv (addr_taken_stmt s) cenv →
    match find_label lbl s k with
    | none => find_label lbl ts tk = none
    | some (s', k') => ∃ ts' tk', find_label lbl ts tk = some (ts', tk') ∧
        compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
        match_cont cfg prog f cenv k' tk' m bound tbound

def simpl_find_label_lsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (prog : program) f cenv m bound tbound lbl ls k tls tk,
    simpl_lblstmt cfg cenv ls = .OK tls →
    match_cont cfg prog f cenv k tk m bound tbound →
    compat_cenv (addr_taken_lblstmt ls) cenv →
    match find_label_ls lbl ls k with
    | none => find_label_ls lbl tls tk = none
    | some (s', k') => ∃ ts' tk', find_label_ls lbl tls tk = some (ts', tk') ∧
        compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
        match_cont cfg prog f cenv k' tk' m bound tbound

def find_label_store_paramsStatement : Prop :=
  ∀ lbl cenv s k params,
    find_label lbl (store_params cenv params s) k = find_label lbl s k

def find_label_add_debug_varsStatement : Prop :=
  ∀ cfg lbl s k vars,
    find_label lbl (add_debug_vars cfg vars s) k = find_label lbl s k

def find_label_add_debug_paramsStatement : Prop :=
  ∀ cfg lbl s k vars,
    find_label lbl (add_debug_params cfg vars s) k = find_label lbl s k

def step_simulationStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p tp : program),
    match_prog cfg p tp →
    let ge := globalenv p
    let tge := globalenv tp
    ∀ S1 t S2,
      step1
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi ge S1 t S2 →
      ∀ S1',
      match_states cfg p S1 S1' →
      ∃ S2',
        plus
          (step2
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate) xi)
          tge S1' t S2' ∧ match_states cfg p S2 S2'

def initial_states_simulationStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p tp : program), match_prog cfg p tp →
    ∀ S, initial_state p S → ∃ R, initial_state tp R ∧
      match_states cfg p S R

def final_states_simulationStatement : Prop :=
  ∀ (cfg : CompilerConfig) (p : program) S R result,
    match_states cfg p S R → final_state S result → final_state R result

def transf_program_correctStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (xi : ExternalCalls) (p tp : program),
    match_prog cfg p tp →
    forward_simulation
      (semantics1
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi p)
      (semantics2
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) xi tp)

def TransfSimplLocalsLinkStatement
    (cfg : CompilerConfig)
    (clightLinkerCertificate : Ctypes.Linker_program_obligations) : Prop :=
  @CompCert4Lean.Common.Linking.TransfLink program program
    (Ctypes.Linker_program function clightLinkerCertificate)
    (Ctypes.Linker_program function clightLinkerCertificate)
    (match_prog cfg)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

namespace VSF

private abbrev proof_F := CompCert4Lean.Cfrontend.SimplLocals.VSet.MFProvider

theorem add_iff_proof : add_iff := by
  intro s x y
  constructor
  · intro h
    by_cases heq : proof_F.E.eq x y
    · exact Or.inl heq
    · exact Or.inr (proof_F.M.add_3 s x y heq h)
  · intro h
    cases h with
    | inl heq => exact proof_F.M.add_1 s x y heq
    | inr hin => exact proof_F.M.add_2 s x y hin

theorem empty_iff_proof : empty_iff := by
  intro x
  constructor
  · intro h
    exact (proof_F.M.empty_1 x) h
  · intro h
    exact False.elim h

theorem mem_iff_proof : mem_iff := by
  intro s x
  constructor
  · intro h
    exact proof_F.M.mem_1 s x h
  · intro h
    exact proof_F.M.mem_2 s x h

end VSF

private theorem compat_union_left (a b : VSet.t) (cenv : compilenv) :
    compat_cenv (VSet.union a b) cenv → compat_cenv a cenv := by
  intro h id ha hc
  exact h id (VSet.MFProvider.M.union_2 a b id ha) hc

private theorem compat_union_right (a b : VSet.t) (cenv : compilenv) :
    compat_cenv (VSet.union a b) cenv → compat_cenv b cenv := by
  intro h id hb hc
  exact h id (VSet.MFProvider.M.union_3 a b id hb) hc

private theorem compat_seq_of_labeled_statement (ls : labeled_statements) (cenv : compilenv) :
    compat_cenv (addr_taken_lblstmt ls) cenv →
      compat_cenv (addr_taken_stmt (seq_of_labeled_statement ls)) cenv := by
  let P : statement → Prop := fun _ => True
  let P0 : labeled_statements → Prop := fun ls =>
    compat_cenv (addr_taken_lblstmt ls) cenv →
      compat_cenv (addr_taken_stmt (seq_of_labeled_statement ls)) cenv
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec (motive_1 := P) (motive_2 := P0)
    all_goals try simp [P]
    case LSnil =>
      intro _ id h
      exact False.elim ((VSet.MFProvider.M.empty_1 id) h)
    case LScons =>
      intro case stmt rest ih h id hu hc
      rcases VSet.MFProvider.M.union_1 _ _ id hu with hs | hr
      · exact h id (VSet.MFProvider.M.union_2 _ _ id hs) hc
      · exact (ih (compat_union_right _ _ _ h)) id hr hc
  exact H ls

private theorem simpl_seq_of_labeled_statement (cfg : CompilerConfig) (cenv : compilenv)
    (ls tls : labeled_statements) :
    simpl_lblstmt cfg cenv ls = .OK tls →
      simpl_stmt cfg cenv (seq_of_labeled_statement ls) =
        .OK (seq_of_labeled_statement tls) := by
  let P : statement → Prop := fun _ => True
  let P0 : labeled_statements → Prop := fun ls =>
    ∀ tls, simpl_lblstmt cfg cenv ls = .OK tls →
      simpl_stmt cfg cenv (seq_of_labeled_statement ls) =
        .OK (seq_of_labeled_statement tls)
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec (motive_1 := P) (motive_2 := P0)
    all_goals try simp [P]
    case LSnil => simp [P0, simpl_lblstmt, simpl_stmt, seq_of_labeled_statement]
    case LScons =>
      intro case stmt rest ih tls h
      simp only [simpl_lblstmt, simpl_stmt, seq_of_labeled_statement] at h ⊢
      split at h <;> try contradiction
      rename_i hstmt
      split at h <;> try contradiction
      rename_i hrest
      cases h
      rw [ih _ hrest]
      rfl
  exact H ls tls

private theorem find_label_Sset_debug_none (cfg : CompilerConfig) (lbl id : ident)
    (ty : type) (a : expr) (k : cont) :
    find_label lbl (Sset_debug cfg id ty a) k = none := by
  unfold Sset_debug
  split <;> rfl

theorem simpl_find_label_ls : simpl_find_label_lsStatement := by
  intro cfg prog f cenv m bound tbound lbl ls
  let P : statement → Prop := fun s =>
    ∀ k ts tk, simpl_stmt cfg cenv s = .OK ts →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_stmt s) cenv →
      match find_label lbl s k with
      | none => find_label lbl ts tk = none
      | some (s', k') => ∃ ts' tk', find_label lbl ts tk = some (ts', tk') ∧
          compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
          match_cont cfg prog f cenv k' tk' m bound tbound
  let P0 : labeled_statements → Prop := fun ls =>
    ∀ k tls tk, simpl_lblstmt cfg cenv ls = .OK tls →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_lblstmt ls) cenv →
      match find_label_ls lbl ls k with
      | none => find_label_ls lbl tls tk = none
      | some (s', k') => ∃ ts' tk', find_label_ls lbl tls tk = some (ts', tk') ∧
          compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
          match_cont cfg prog f cenv k' tk' m bound tbound
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec (motive_1 := P) (motive_2 := P0)
    case Sskip =>
      intro k ts tk h _ _
      cases h
      rfl
    case Sassign =>
      intro lhs rhs k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h
      · cases h
        exact find_label_Sset_debug_none cfg lbl _ _ _ tk
      · cases h
        rfl
    case Sset =>
      intro id rhs k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Scall =>
      intro result fn args k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Sbuiltin =>
      intro result ef argTypes args k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Ssequence =>
      intro s1 s2 ih1 ih2 k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i h1
      split at h <;> try contradiction
      rename_i h2
      cases h
      have compat1 : compat_cenv (addr_taken_stmt s1) cenv :=
        compat_union_left _ _ _ compat
      have compat2 : compat_cenv (addr_taken_stmt s2) cenv :=
        compat_union_right _ _ _ compat
      have mc1 := match_Kseq cenv s2 k _ tk m bound tbound h2 mc compat2
      have h1' := ih1 (.Kseq s2 k) _ (.Kseq _ tk) h1 mc1 compat1
      cases e : find_label lbl s1 (.Kseq s2 k) with
      | none =>
          simp [e] at h1'
          simpa [find_label, e, h1'] using ih2 k _ tk h2 mc compat2
      | some found =>
          rcases (by simpa [e] using h1') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sloop =>
      intro body iter ihbody ihiter k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hbody
      split at h <;> try contradiction
      rename_i hiter
      cases h
      have compatbody : compat_cenv (addr_taken_stmt body) cenv :=
        compat_union_left _ _ _ compat
      have compatiter : compat_cenv (addr_taken_stmt iter) cenv :=
        compat_union_right _ _ _ compat
      have mcbody := match_Kloop1 cenv body iter k _ _ tk m bound tbound
        hbody hiter mc compat
      have hbody' := ihbody (.Kloop1 body iter k) _ (.Kloop1 _ _ tk)
        hbody mcbody compatbody
      cases e : find_label lbl body (.Kloop1 body iter k) with
      | none =>
          simp [e] at hbody'
          have mciter := match_Kloop2 cenv body iter k _ _ tk m bound tbound
            hbody hiter mc compat
          simpa [find_label, e, hbody'] using
            ihiter (.Kloop2 body iter k) _ (.Kloop2 _ _ tk) hiter mciter compatiter
      | some found =>
          rcases (by simpa [e] using hbody') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sswitch =>
      intro selector cases ihcases k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hcases
      cases h
      have compatcases : compat_cenv (addr_taken_lblstmt cases) cenv :=
        compat_union_right _ _ _ compat
      have mc' := match_Kswitch cenv k tk m bound tbound mc
      simpa [find_label] using ihcases (.Kswitch k) _ (.Kswitch tk) hcases mc' compatcases
    case Slabel =>
      intro l body ihbody k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hbody
      cases h
      have compatbody : compat_cenv (addr_taken_stmt body) cenv := by
        simpa [addr_taken_stmt] using compat
      cases e : CompCert4Lean.Common.AST.ident_eq lbl l with
      | left heq =>
          simp only [find_label, e]
          exact ⟨_, tk, rfl, compatbody, hbody, mc⟩
      | right hne =>
          simpa [find_label, e] using ihbody k _ tk hbody mc compatbody
    case Sifthenelse =>
      intro cond s1 s2 ih1 ih2 k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i h1
      split at h <;> try contradiction
      rename_i h2
      cases h
      have compat12 : compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv :=
        compat_union_right _ _ _ compat
      have compat1 : compat_cenv (addr_taken_stmt s1) cenv :=
        compat_union_left _ _ _ compat12
      have compat2 : compat_cenv (addr_taken_stmt s2) cenv :=
        compat_union_right _ _ _ compat12
      have h1' := ih1 k _ tk h1 mc compat1
      cases e : find_label lbl s1 k with
      | none =>
          simp [e] at h1'
          simpa [find_label, e, h1'] using ih2 k _ tk h2 mc compat2
      | some found =>
          rcases (by simpa [e] using h1') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sbreak =>
      intro k ts tk h _ _
      cases h
      rfl
    case Scontinue =>
      intro k ts tk h _ _
      cases h
      rfl
    case Sreturn =>
      intro result k ts tk h _ _
      cases h
      rfl
    case Sgoto =>
      intro l k ts tk h _ _
      cases h
      rfl
    case LSnil =>
      intro k tls tk h _ _
      cases h
      rfl
    case LScons =>
      intro case stmt rest ihstmt ihrest k tls tk h mc compat
      simp only [simpl_lblstmt] at h
      split at h <;> try contradiction
      rename_i hstmt
      split at h <;> try contradiction
      rename_i hrest
      cases h
      have compatstmt : compat_cenv (addr_taken_stmt stmt) cenv :=
        compat_union_left _ _ _ compat
      have compatrest : compat_cenv (addr_taken_lblstmt rest) cenv :=
        compat_union_right _ _ _ compat
      have hseq := simpl_seq_of_labeled_statement cfg cenv rest _ hrest
      have compatseq := compat_seq_of_labeled_statement rest cenv compatrest
      have mcstmt := match_Kseq cenv (seq_of_labeled_statement rest) k
        (seq_of_labeled_statement _) tk m bound tbound hseq mc compatseq
      have hstmt' := ihstmt (.Kseq (seq_of_labeled_statement rest) k) _
        (.Kseq (seq_of_labeled_statement _) tk) hstmt mcstmt compatstmt
      cases e : find_label lbl stmt (.Kseq (seq_of_labeled_statement rest) k) with
      | none =>
          simp [e] at hstmt'
          simpa [find_label_ls, e, hstmt'] using ihrest k _ tk hrest mc compatrest
      | some found =>
          rcases (by simpa [e] using hstmt') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label_ls, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
  exact H ls

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib

private theorem simplLocals_transf_globdefs_match
    (cfg : CompilerConfig) (p : Clight.program) :
    ∀ (l : List (ident × CompCert4Lean.Common.AST.globdef Clight.fundef Ctypes.type))
      (defs : List (ident × CompCert4Lean.Common.AST.globdef Clight.fundef Ctypes.type)),
      transf_globdefs (fun _ f => transf_fundef cfg f) (fun _ v => .OK v) l = .OK defs →
      list_forall2
        (match_ident_globdef
          (fun _ f tf => transf_fundef cfg f = .OK tf) Eq
          (Ctypes.program_of_program p)) l defs := by
  intro l
  induction l with
  | nil =>
      intro defs hdefs
      simp [transf_globdefs] at hdefs
      subst defs
      exact list_forall2.nil _
  | cons hd tl ih =>
      intro defs hdefs
      cases hd with
      | mk id gd =>
          cases gd with
          | Gfun f =>
              cases htf : transf_fundef cfg f with
              | Error msg => simp [transf_globdefs, htf] at hdefs
              | OK tf =>
                  cases htail : transf_globdefs
                      (fun _ f => transf_fundef cfg f) (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, htf, htail] at hdefs
                  | OK defsTail =>
                      simp [transf_globdefs, htf, htail] at hdefs
                      subst defs
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · apply match_globdef_fun (ctx' := Ctypes.program_of_program p)
                          · exact linkorder_refl _
                          · exact htf
                      · exact ih defsTail htail
          | Gvar v =>
              cases v with
              | mk info init readonly volatile =>
                  cases htail : transf_globdefs
                      (fun _ f => transf_fundef cfg f) (fun _ v => .OK v) tl with
                  | Error msg => simp [transf_globdefs, transf_globvar, htail] at hdefs
                  | OK defsTail =>
                      simp [transf_globdefs, transf_globvar, htail] at hdefs
                      subst defs
                      apply list_forall2.cons
                      · constructor
                        · rfl
                        · apply match_globdef_var
                          exact match_globvar_intro _ _ _ _ _ _ rfl
                      · exact ih defsTail htail

theorem match_transf_program : match_transf_programStatement := by
  intro cfg p tp h
  unfold transf_program at h
  unfold match_prog
  unfold transform_partial_program transform_partial_program2 at h
  cases hdefs : transf_globdefs
      (fun _ f => transf_fundef cfg f) (fun _ v => .OK v)
      (Ctypes.program_of_program p).prog_defs with
  | Error msg => simp [hdefs] at h
  | OK defs =>
      simp [hdefs] at h
      injection h with hEq
      unfold match_program match_program_gen
      have hdefsEq : (Ctypes.program_of_program tp).prog_defs = defs := by
        exact (congrArg (fun q : Clight.program => q.prog_defs) hEq).symm
      have hmainEq : (Ctypes.program_of_program tp).prog_main =
          (Ctypes.program_of_program p).prog_main := by
        exact (congrArg (fun q : Clight.program => q.prog_main) hEq).symm
      have hpublicEq : (Ctypes.program_of_program tp).prog_public =
          (Ctypes.program_of_program p).prog_public := by
        exact (congrArg (fun q : Clight.program => q.prog_public) hEq).symm
      apply And.intro
      · apply And.intro
        · rw [hdefsEq]
          exact simplLocals_transf_globdefs_match cfg p _ _ hdefs
        · exact ⟨hmainEq, hpublicEq⟩
      · exact (congrArg (fun q : Clight.program => q.prog_types) hEq).symm

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem comp_env_preserved : comp_env_preservedStatement := by
  intro cfg p tp hmatch
  have htypes : tp.prog_types = p.prog_types := hmatch.2
  change tp.prog_comp_env = p.prog_comp_env
  have hp : Ctypes.build_composite_env p.prog_types = .OK p.prog_comp_env :=
    p.prog_comp_env_eq
  have htp : Ctypes.build_composite_env tp.prog_types = .OK tp.prog_comp_env :=
    tp.prog_comp_env_eq
  rw [htypes] at htp
  apply CompCert4Lean.Common.Errors.res.OK.inj
  exact htp.symm.trans hp

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem simpllocalsproof_add_global_match
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W)
    (h : Genv.match_genvs R ge1 ge2)
    (id : ident) (g1 : globdef A V) (g2 : globdef B W) (hr : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1)) (Genv.add_global ge2 (id, g2)) := by
  change positive at id
  constructor
  · simp only [Genv.add_global]
    change PArith.BinPos.Pos.succ ge2.genv_next = PArith.BinPos.Pos.succ ge1.genv_next
    exact congrArg _ h.mge_next
  · intro id'
    simp only [Genv.add_global]
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    have hx2 := @PTree.gsspec_proof _ id' id ge2.genv_next ge2.genv_symb
    have hx1 := @PTree.gsspec_proof _ id' id ge1.genv_next ge1.genv_symb
    cases heq : peq id' id with
    | left hij =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            some ge2.genv_next := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            some ge1.genv_next := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_next]
    | right hne =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            PTree.get id' ge2.genv_symb := by
          simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            PTree.get id' ge1.genv_symb := by
          simpa [heq] using hx1
        rw [hx2', hx1', h.mge_symb]
  · intro b
    simp only [Genv.add_global]
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have hx1 := @PTree.gsspec_proof _ b ge1.genv_next g1 ge1.genv_defs
    have hx2 := @PTree.gsspec_proof _ b ge2.genv_next g2 ge2.genv_defs
    cases heq : peq b ge1.genv_next with
    | left hb =>
        have heq' : b = ge2.genv_next := hb.trans h.mge_next.symm
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2 =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                some g1 := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                some g2 := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact option_rel.some g1 g2 hr
        | right hb2 => exact False.elim (hb2 heq')
    | right hb =>
        have hb2 : b ≠ ge2.genv_next := by
          intro hbeq
          apply hb
          exact hbeq.trans h.mge_next
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2' => exact False.elim (hb (hb2'.trans h.mge_next))
        | right hb2' =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                PTree.get b ge1.genv_defs := by
              simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                PTree.get b ge2.genv_defs := by
              simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact h.mge_defs b

private theorem simpllocalsproof_add_globals_match
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (gl1 : List (ident × globdef A V)) (gl2 : List (ident × globdef B W))
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) :
    list_forall2 (fun x y => x.1 = y.1 ∧ R x.2 y.2) gl1 gl2 →
    Genv.match_genvs R ge1 ge2 →
    Genv.match_genvs R (Genv.add_globals ge1 gl1) (Genv.add_globals ge2 gl2) := by
  intro hlist hge
  induction hlist generalizing ge1 ge2 with
  | nil => exact hge
  | cons hd1 hd2 hhd htl ih =>
      rcases hhd with ⟨hid, hrel⟩
      cases hd1 with
      | mk id1 gd1 =>
          cases hd2 with
          | mk id2 gd2 =>
              simp only [Genv.add_globals, List.foldl]
              change id1 = id2 at hid
              subst id2
              exact ih
                (Genv.add_global ge1 (id1, gd1))
                (Genv.add_global ge2 (id1, gd2))
                (simpllocalsproof_add_global_match R ge1 ge2 hge id1 gd1 gd2 hrel)

private theorem simpllocalsproof_globalenvs_match
    {A B V : Type} [Linker A] [Linker V]
    (transf : A → CompCert4Lean.Common.Errors.res B)
    (p : CompCert4Lean.Common.AST.program A V)
    (tp : CompCert4Lean.Common.AST.program B V)
    (hmatch : match_program (fun _ f tf => transf f = .OK tf) Eq p tp) :
    Genv.match_genvs
      (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
      (Genv.globalenv p) (Genv.globalenv tp) := by
  have hempty : Genv.match_genvs
      (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
      (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _
  exact simpllocalsproof_add_globals_match
    (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
    p.prog_defs tp.prog_defs
    (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public)
    hmatch.1 hempty

theorem symbols_preserved : symbols_preservedStatement := by
  intro cfg p tp hmatch id
  have hgenv := simpllocalsproof_globalenvs_match
    (A := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (B := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (V := type)
    (transf := fun f => CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f)
    (p := Ctypes.program_of_program p) (tp := Ctypes.program_of_program tp) hmatch.1
  exact hgenv.mge_symb id

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem simpllocalsproof_add_globals_public_suffix
    {A V : Type} (ge : Genv.t A V) (gl : List (ident × globdef A V)) :
    (Genv.add_globals ge gl).genv_public = ge.genv_public := by
  induction gl generalizing ge with
  | nil => rfl
  | cons x xs ih =>
      simp only [Genv.add_globals, List.foldl]
      exact ih (Genv.add_global ge x)

private theorem simpllocalsproof_add_global_match_suffix
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (ge1 : Genv.t A V) (ge2 : Genv.t B W)
    (h : Genv.match_genvs R ge1 ge2)
    (id : ident) (g1 : globdef A V) (g2 : globdef B W) (hr : R g1 g2) :
    Genv.match_genvs R (Genv.add_global ge1 (id, g1))
      (Genv.add_global ge2 (id, g2)) := by
  change positive at id
  constructor
  · simp only [Genv.add_global]
    change PArith.BinPos.Pos.succ ge2.genv_next = PArith.BinPos.Pos.succ ge1.genv_next
    exact congrArg _ h.mge_next
  · intro id'
    simp only [Genv.add_global]
    change PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
      PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb)
    have hx2 := @PTree.gsspec_proof _ id' id ge2.genv_next ge2.genv_symb
    have hx1 := @PTree.gsspec_proof _ id' id ge1.genv_next ge1.genv_symb
    cases heq : peq id' id with
    | left hij =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            some ge2.genv_next := by simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            some ge1.genv_next := by simpa [heq] using hx1
        rw [hx2', hx1', h.mge_next]
    | right hne =>
        have hx2' : PTree.get id' (PTree.set id ge2.genv_next ge2.genv_symb) =
            PTree.get id' ge2.genv_symb := by simpa [heq] using hx2
        have hx1' : PTree.get id' (PTree.set id ge1.genv_next ge1.genv_symb) =
            PTree.get id' ge1.genv_symb := by simpa [heq] using hx1
        rw [hx2', hx1', h.mge_symb]
  · intro b
    simp only [Genv.add_global]
    change option_rel R
      (PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs))
      (PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs))
    have hx1 := @PTree.gsspec_proof _ b ge1.genv_next g1 ge1.genv_defs
    have hx2 := @PTree.gsspec_proof _ b ge2.genv_next g2 ge2.genv_defs
    cases heq : peq b ge1.genv_next with
    | left hb =>
        have heq' : b = ge2.genv_next := hb.trans h.mge_next.symm
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2 =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                some g1 := by simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                some g2 := by simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact option_rel.some g1 g2 hr
        | right hb2 => exact False.elim (hb2 heq')
    | right hb =>
        have hb2 : b ≠ ge2.genv_next := by
          intro hbeq
          apply hb
          exact hbeq.trans h.mge_next
        cases hpeq2 : peq b ge2.genv_next with
        | left hb2' => exact False.elim (hb (hb2'.trans h.mge_next))
        | right hb2' =>
            have hx1' : PTree.get b (PTree.set ge1.genv_next g1 ge1.genv_defs) =
                PTree.get b ge1.genv_defs := by simpa [heq] using hx1
            have hx2' : PTree.get b (PTree.set ge2.genv_next g2 ge2.genv_defs) =
                PTree.get b ge2.genv_defs := by simpa [hpeq2] using hx2
            rw [hx1', hx2']
            exact h.mge_defs b

private theorem simpllocalsproof_add_globals_match_suffix
    {A B V W : Type} (R : globdef A V → globdef B W → Prop)
    (gl1 : List (ident × globdef A V)) (gl2 : List (ident × globdef B W))
    (ge1 : Genv.t A V) (ge2 : Genv.t B W) :
    list_forall2 (fun x y => x.1 = y.1 ∧ R x.2 y.2) gl1 gl2 →
    Genv.match_genvs R ge1 ge2 →
    Genv.match_genvs R (Genv.add_globals ge1 gl1) (Genv.add_globals ge2 gl2) := by
  intro hlist hge
  induction hlist generalizing ge1 ge2 with
  | nil => exact hge
  | cons hd1 hd2 hhd htl ih =>
      rcases hhd with ⟨hid, hrel⟩
      cases hd1 with
      | mk id1 gd1 =>
          cases hd2 with
          | mk id2 gd2 =>
              simp only [Genv.add_globals, List.foldl]
              change id1 = id2 at hid
              subst id2
              exact ih
                (Genv.add_global ge1 (id1, gd1))
                (Genv.add_global ge2 (id1, gd2))
                (simpllocalsproof_add_global_match_suffix R ge1 ge2 hge id1 gd1 gd2 hrel)

private theorem simpllocalsproof_globalenvs_match_suffix
    {A B V : Type} [Linker A] [Linker V]
    (transf : A → CompCert4Lean.Common.Errors.res B)
    (p : CompCert4Lean.Common.AST.program A V)
    (tp : CompCert4Lean.Common.AST.program B V)
    (hmatch : match_program (fun _ f tf => transf f = .OK tf) Eq p tp) :
    Genv.match_genvs
      (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
      (Genv.globalenv p) (Genv.globalenv tp) := by
  have hempty : Genv.match_genvs
      (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
      (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public) := by
    constructor
    · rfl
    · intro id
      rfl
    · intro b
      exact option_rel.none _
  exact simpllocalsproof_add_globals_match_suffix
    (match_globdef (fun _ f tf => transf f = .OK tf) Eq p)
    p.prog_defs tp.prog_defs
    (Genv.empty_genv A V p.prog_public) (Genv.empty_genv B V tp.prog_public)
    hmatch.1 hempty

theorem senv_preserved : senv_preservedStatement := by
  intro cfg p tp hmatch
  have hgenv := simpllocalsproof_globalenvs_match_suffix
    (A := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (B := CompCert4Lean.Cfrontend.Ctypes.fundef CompCert4Lean.Cfrontend.Clight.function)
    (V := type)
    (transf := fun f => CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f)
    (p := Ctypes.program_of_program p) (tp := Ctypes.program_of_program tp) hmatch.1
  unfold Senv.equiv
  constructor
  · intro id
    exact hgenv.mge_symb id
  constructor
  · intro id
    change Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program tp)) id =
      Genv.public_symbol (Genv.globalenv (Ctypes.program_of_program p)) id
    have ht : (Genv.globalenv (Ctypes.program_of_program tp)).genv_public = tp.prog_public := by
      unfold Genv.globalenv
      exact simpllocalsproof_add_globals_public_suffix _ _
    have hp : (Genv.globalenv (Ctypes.program_of_program p)).genv_public = p.prog_public := by
      unfold Genv.globalenv
      exact simpllocalsproof_add_globals_public_suffix _ _
    unfold Genv.public_symbol Genv.find_symbol
    rw [hgenv.mge_symb id, ht, hp]
    have hpub : tp.prog_public = p.prog_public := hmatch.1.2.2
    rw [hpub]
  · intro b
    change Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program tp)) b =
      Genv.block_is_volatile (Genv.globalenv (Ctypes.program_of_program p)) b
    unfold Genv.block_is_volatile Genv.find_var_info Genv.find_def
    cases h1 : PTree.get b (Genv.globalenv (Ctypes.program_of_program p)).genv_defs with
    | none =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none => rfl
        | some gd2 =>
            have hd := hgenv.mge_defs b
            simp [h1, h2] at hd
            cases hd
    | some gd1 =>
        cases h2 : PTree.get b (Genv.globalenv (Ctypes.program_of_program tp)).genv_defs with
        | none =>
            have hd := hgenv.mge_defs b
            simp [h1, h2] at hd
            cases hd
        | some gd2 =>
            have hd := hgenv.mge_defs b
            simp [h1, h2] at hd
            cases hd with
            | some x y hrel =>
                cases hrel with
                | match_globdef_fun ctx' f1 f2 horder htrans => rfl
                | match_globdef_var v1 v2 hvar =>
                    cases hvar
                    rfl

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem type_of_fundef_preserved : type_of_fundef_preservedStatement := by
  intro cfg fd tfd h
  cases fd with
  | External ef args result cc =>
      simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef] at h
      cases h
      rfl
  | Internal f =>
      unfold CompCert4Lean.Cfrontend.SimplLocals.transf_fundef at h
      cases htrans : CompCert4Lean.Cfrontend.SimplLocals.transf_function cfg f with
      | Error msg =>
          simp [htrans] at h
      | OK transformed =>
          simp [htrans] at h
          cases h
          simp [CompCert4Lean.Cfrontend.Clight.type_of_fundef,
            CompCert4Lean.Cfrontend.Clight.type_of_function] at ⊢
          unfold CompCert4Lean.Cfrontend.SimplLocals.transf_function at htrans
          split at htrans
          · cases hbody : CompCert4Lean.Cfrontend.SimplLocals.simpl_stmt cfg
                (CompCert4Lean.Cfrontend.SimplLocals.cenv_for f) f.fn_body with
            | Error message =>
                simp [hbody] at htrans
            | OK body' =>
                simp [hbody] at htrans
                cases htrans
                simp
          · cases htrans

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

private theorem simpllocalsproof_val_inject_incr
    {f f' : meminj} {v v' : val}
    (hinc : inject_incr f f') (hval : Val.inject f v v') :
    Val.inject f' v v' := by
  cases hval with
  | inject_int n => exact Val.inject.inject_int n
  | inject_long n => exact Val.inject.inject_long n
  | inject_float x => exact Val.inject.inject_float x
  | inject_single x => exact Val.inject.inject_single x
  | inject_ptr b ofs b' ofs' delta hmap hofs =>
      exact Val.inject.inject_ptr b ofs b' ofs' delta (hinc b b' delta hmap) hofs
  | val_inject_undef => exact Val.inject.val_inject_undef _

theorem match_envs_invariant : match_envs_invariantStatement := by
  intro f cenv e le m lo hi te tle tlo thi f' m' hme hload hincr hinv1 hinv2
  rcases hme with ⟨hvars, htemps, hinj, hrange, htrange, hmapped, hflat, hlo, htlo⟩
  refine ⟨?_, ?_, hinj, hrange, htrange, ?_, ?_, hlo, htlo⟩
  · intro id
    cases hvars id with
    | match_var_lifted b ty chunk v tv henv htenv hlift hmap hmode hload0 htlenv hv =>
        have hbounds : Ple lo b ∧ Plt b hi := hrange id b ty henv
        have hmap' : f' b = none := by
          rw [hinv1 b hbounds, hmap]
        have hload' : Mem.load chunk m' b (.Z0 : Z) = some v :=
          hload b chunk v hmap hbounds hload0
        exact match_var_lifted b ty chunk v tv henv htenv hlift hmap' hmode hload'
          htlenv (simpllocalsproof_val_inject_incr hincr hv)
    | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
        exact match_var_not_lifted b ty b' henv htenv hnlocal
          (hincr b b' (.Z0 : Z) hmap)
    | match_var_not_local henv htenv hnlocal =>
        exact match_var_not_local henv htenv hnlocal
  · intro id v hle
    rcases htemps id v hle with ⟨⟨tv, htle, hv⟩, hcenv⟩
    exact ⟨⟨tv, htle, simpllocalsproof_val_inject_incr hincr hv⟩, hcenv⟩
  · intro id b' ty hte
    rcases hmapped id b' ty hte with ⟨b, hmap, henv⟩
    exact ⟨b, hincr b b' (.Z0 : Z) hmap, henv⟩
  · intro id b' ty b delta hte hmap'
    have hmap : f b = some (b', delta) :=
      (hinv2 b b' delta hmap' (htrange id b' ty hte)).symm.trans hmap'
    exact hflat id b' ty b delta hte hmap

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem val_casted_load_result : val_casted_load_resultStatement := by
  intro v ty chunk hcast hmode
  cases hcast with
  | val_casted_int sz si attr n hcast =>
      cases sz <;> cases si <;> simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        simpa [CompCert4Lean.Common.Values.Val.load_result,
          CompCert4Lean.Cfrontend.Cop.cast_int_int] using congrArg
            CompCert4Lean.Common.Values.val.Vint hcast
      · cases hmode
        by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
      · cases hmode
        by_cases hn : CompCert4Lean.Lib.Integers.Int.eq n
            CompCert4Lean.Lib.Integers.Int.zero
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
        · simp [CompCert4Lean.Common.Values.Val.load_result,
            CompCert4Lean.Cfrontend.Cop.cast_int_int, hn] at hcast ⊢
          cases hcast
          rfl
  | val_casted_float attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      cases hmode
      rfl
  | val_casted_single attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      cases hmode
      rfl
  | val_casted_long si attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode] at hmode
      cases hmode
      rfl
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode,
        CompCert4Lean.Common.AST.Mptr,
        CompCert4Lean.X86_64.Archi.ptr64] at hmode
      cases hmode
      simp [CompCert4Lean.Common.Values.Val.load_result,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode,
        CompCert4Lean.Common.AST.Mptr, hptr64] at hmode
      cases hmode
      rfl
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode,
        CompCert4Lean.Common.AST.Mptr, hptr64] at hmode
      cases hmode
      rfl
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.access_mode, hptr64] at hmode
      cases hmode
      rfl
  | val_casted_struct id attr b ofs =>
      cases hmode
  | val_casted_union id attr b ofs =>
      cases hmode
  | val_casted_void v =>
      cases hmode

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem val_casted_inject : val_casted_injectStatement := by
  intro f v v' ty hinj hcast
  cases hinj <;> cases hcast <;> constructor <;> assumption

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem forall2_val_casted_inject : forall2_val_casted_injectStatement := by
  intro f vl vl' hinj
  induction hinj with
  | inject_list_nil =>
      intro tyl hcast
      cases hcast
      exact .nil _
  | inject_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      intro tyl hcast
      cases hcast with
      | cons _ _ hty htys =>
          exact .cons _ _ (val_casted_inject f v1 v2 _ hhead hty) (ih _ htys)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem val_casted_list_params : val_casted_list_paramsStatement := by
  intro params vl hcast
  induction params generalizing vl with
  | nil =>
      cases hcast
      exact .nil _
  | cons p ps ih =>
      cases p with
      | mk id ty =>
          cases hcast with
          | cons _ _ _ _ hhead htail =>
              exact .cons _ _ hhead (ih _ htail)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem step_Sdebug_var
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_Sdebug_varStatement := by
  intro xi tprog f id ty k e le m b henv
  unfold CompCert4Lean.Cfrontend.SimplLocals.Sdebug_var
  change CompCert4Lean.Cfrontend.Clight.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi
    (CompCert4Lean.Cfrontend.Clight.globalenv tprog)
      (CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog)) _ _ _
  refine CompCert4Lean.Cfrontend.Clight.step.step_builtin
    (xi := xi)
    (ge := CompCert4Lean.Cfrontend.Clight.globalenv tprog)
    (function_entry := CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog))
    (f := f) (result := none)
    (ef := .EF_debug (.xI (.xO .xH)) id [CompCert4Lean.Common.AST.Tptr])
    (argTypes := [.Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr])
    (args := [.Eaddrof (.Evar id ty) (.Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr)])
    (k := k) (e := e) (le := le) (m := m)
    (vargs := [.Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero])
    (t := CompCert4Lean.Common.Events.E0) (vres := .Vundef) (m' := m) ?_ ?_
  · refine CompCert4Lean.Cfrontend.Clight.eval_exprlist.cons
      (a := .Eaddrof (.Evar id ty) (.Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr))
      (rest := []) (ty := .Tpointer ty CompCert4Lean.Cfrontend.Ctypes.noattr)
      (types := []) (v1 := .Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero)
      (v2 := .Vptr b CompCert4Lean.Lib.Integers.Ptrofs.zero) (values := []) ?_ ?_
      CompCert4Lean.Cfrontend.Clight.eval_exprlist.nil
    · exact CompCert4Lean.Cfrontend.Clight.eval_expr.eval_Eaddrof _ _ _ _
        (CompCert4Lean.Cfrontend.Clight.eval_lvalue.eval_Evar_local _ _ _ henv)
    · simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Clight.typeof,
        CompCert4Lean.X86_64.Archi.ptr64]
  · exact CompCert4Lean.Common.Events.extcall_debug_sem.extcall_debug_sem_intro _ _

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem cast_typeconv
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    cast_typeconvStatement := by
  intro v ty m h
  cases h with
  | val_casted_int sz si attr n hcast =>
      cases sz <;> cases si <;>
        simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
          CompCert4Lean.Cfrontend.Cop.classify_cast,
          CompCert4Lean.Cfrontend.Ctypes.typeconv,
          CompCert4Lean.Cfrontend.Ctypes.type_int32s,
          CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
          CompCert4Lean.Cfrontend.Ctypes.change_attributes,
          CompCert4Lean.Cfrontend.Cop.cast_int_int,
          CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_float attr n =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_single attr n =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_long si attr n =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64, hptr64]
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64, hptr64]
  | val_casted_struct id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_union id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_void v =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast,
        CompCert4Lean.Cfrontend.Cop.classify_cast,
        CompCert4Lean.Cfrontend.Ctypes.typeconv,
        CompCert4Lean.Cfrontend.Ctypes.type_int32s,
        CompCert4Lean.Cfrontend.Ctypes.remove_attributes,
        CompCert4Lean.Cfrontend.Ctypes.change_attributes,
        CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem step_Sdebug_temp
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_Sdebug_tempStatement := by
  intro xi tprog f id ty k e le m v hfind hcasted
  unfold CompCert4Lean.Cfrontend.SimplLocals.Sdebug_temp
  change CompCert4Lean.Cfrontend.Clight.step
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi
    (CompCert4Lean.Cfrontend.Clight.globalenv tprog)
    (CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog)) _ _ _
  refine CompCert4Lean.Cfrontend.Clight.step.step_builtin
    (xi := xi)
    (ge := CompCert4Lean.Cfrontend.Clight.globalenv tprog)
    (function_entry := CompCert4Lean.Cfrontend.Clight.function_entry2
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog))
    (f := f) (result := none)
    (ef := .EF_debug (.xO .xH) id
      [CompCert4Lean.Cfrontend.Ctypes.typ_of_type ty])
    (argTypes := [CompCert4Lean.Cfrontend.Ctypes.typeconv ty])
    (args := [.Etempvar id ty]) (k := k) (e := e) (le := le) (m := m)
    (vargs := [v]) (t := CompCert4Lean.Common.Events.E0) (vres := .Vundef) (m' := m) ?_ ?_
  · refine CompCert4Lean.Cfrontend.Clight.eval_exprlist.cons
      (a := .Etempvar id ty) (rest := [])
      (ty := CompCert4Lean.Cfrontend.Ctypes.typeconv ty) (types := [])
      (v1 := v) (v2 := v) (values := []) ?_ ?_
      CompCert4Lean.Cfrontend.Clight.eval_exprlist.nil
    · exact CompCert4Lean.Cfrontend.Clight.eval_expr.eval_Etempvar _ _ _ hfind
    · exact cast_typeconv v ty m hcasted
  · exact CompCert4Lean.Common.Events.extcall_debug_sem.extcall_debug_sem_intro _ _

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem make_cast_correct
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    make_cast_correctStatement := by
  intro tprog e le m a v1 tto v2 ha hsem
  have hcast : CompCert4Lean.Cfrontend.Clight.eval_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (CompCert4Lean.Cfrontend.Clight.globalenv tprog) e le m
      (.Ecast a tto) v2 :=
    CompCert4Lean.Cfrontend.Clight.eval_expr.cast a tto v1 v2 ha hsem
  unfold CompCert4Lean.Cfrontend.SimplLocals.make_cast
  cases hclass : CompCert4Lean.Cfrontend.Cop.classify_cast
      (CompCert4Lean.Cfrontend.Clight.typeof a) tto with
  | cast_case_pointer =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass,
        CompCert4Lean.X86_64.Archi.ptr64] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_i2i sz2 si2 =>
      cases sz2 with
      | I32 =>
          simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass,
            CompCert4Lean.Cfrontend.Cop.cast_int_int,
            CompCert4Lean.X86_64.Archi.ptr64] at hsem
          cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast,
            CompCert4Lean.Cfrontend.Cop.cast_int_int]
      | I8 =>
          simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
      | I16 =>
          simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
      | IBool =>
          simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2f =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_s2s =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_l2l =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass,
        CompCert4Lean.X86_64.Archi.ptr64] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_struct id1 id2 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_union id1 id2 =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_void =>
      simp [CompCert4Lean.Cfrontend.Cop.sem_cast, hclass] at hsem
      cases v1 <;> simp_all [CompCert4Lean.Cfrontend.SimplLocals.make_cast]
  | cast_case_f2s =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2f =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2f si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2s si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2i sz2 si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2i sz2 si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2bool =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_i2l si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2i sz2 si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2f si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_l2s si1 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_f2l si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_s2l si2 =>
      simpa [CompCert4Lean.Cfrontend.SimplLocals.make_cast] using hcast
  | cast_case_default =>
      exact hcast

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem bind_parameter_temps_inv : bind_parameter_temps_invStatement := by
  intro id params args le le' hbind hnot
  induction params generalizing args le le' with
  | nil =>
      cases args <;> simp [bind_parameter_temps] at hbind
      cases hbind
      rfl
  | cons p params ih =>
      cases p with
      | mk id1 ty1 =>
          cases args with
          | nil => simp [bind_parameter_temps] at hbind
          | cons v args =>
              simp only [bind_parameter_temps] at hbind
              have hnot' : id ∉ var_names params := by
                intro hin
                apply hnot
                simp only [var_names, List.map_cons, List.mem_cons]
                have hin' : id ∈ List.map Prod.fst params := by simpa [var_names] using hin
                exact Or.inr hin'
              have hi := ih (args := args) (le := PTree.set id1 v le) (le' := le') hbind hnot'
              have hget : PTree.get id (PTree.set id1 v le) = PTree.get id le := by
                apply PTree.gso
                intro heq
                apply hnot
                simp [var_names, heq]
              exact hi.trans hget
end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Driver.Compopts
open CompCert4Lean.Lib.Maps

theorem step_add_debug_vars
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_add_debug_varsStatement := by
  intro cfg xi tprog f s e le m vars k h
  unfold add_debug_vars
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · rw [hd]
    induction vars with
    | nil =>
        exact star_refl _ _ _
    | cons p vars ih =>
        cases p with
        | mk id ty =>
            have hb : ∃ b, PTree.get id e = some (b, ty) := h id ty (List.mem_cons_self)
            rcases hb with ⟨b, hbe⟩
            have hrest := fun id' ty' (hm : (id', ty') ∈ vars) =>
              h id' ty' (List.mem_cons_of_mem _ hm)
            apply star_left
            · exact CompCert4Lean.Cfrontend.Clight.step.step_seq f
                (Sdebug_var id ty) (List.foldr add_debug_var s vars) k e le m
            · apply star_left
              · exact step_Sdebug_var xi tprog f id ty
                  (.Kseq (List.foldr add_debug_var s vars) k) e le m b hbe
              · apply star_left
                · exact CompCert4Lean.Cfrontend.Clight.step.step_skip_seq f
                    (List.foldr add_debug_var s vars) k e le m
                · exact ih hrest
                · rfl
              · rfl
            · rfl
  · simp [hd]
    exact star_refl _ _ _
end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Driver.Compopts

theorem step_add_debug_params
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_add_debug_paramsStatement := by
  intro cfg xi tprog f s k e le m params vl le1 hnr hcast hbind
  unfold add_debug_params
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · rw [hd]
    induction params generalizing vl le1 le with
    | nil =>
        cases vl with
        | nil =>
            cases hcast
            cases hbind
            exact star_refl _ _ _
        | cons v vl =>
            cases hcast
    | cons p params ih =>
        cases p with
        | mk id ty =>
            cases vl with
            | nil => cases hcast
            | cons v vl =>
                cases hcast with
                | cons _ _ hvc hvcTail =>
                    cases hnr with
                    | cons _ hnotmem hnrTail =>
                        have hidnot : id ∉ var_names params := by
                            intro hm
                            exact hnotmem (by simpa [var_names] using hm)
                        have hle' := bind_parameter_temps_inv id params vl
                            (PTree.set id v le1) le hbind hidnot
                        have hget : PTree.get id le = some v := by
                            exact hle'.trans (PTree.gss id v le1)
                        have hrest := ih (le := le) (vl := vl)
                            (le1 := PTree.set id v le1) hnrTail hvcTail hbind
                        apply star_left
                        · exact CompCert4Lean.Cfrontend.Clight.step.step_seq f
                            (Sdebug_temp id ty) (List.foldr add_debug_param s params) k e le m
                        · apply star_left
                          · exact step_Sdebug_temp xi tprog f id ty
                              (.Kseq (List.foldr add_debug_param s params) k) e le m v hget hvc
                          · apply star_left
                            · exact CompCert4Lean.Cfrontend.Clight.step.step_skip_seq f
                                (List.foldr add_debug_param s params) k e le m
                            · exact hrest
                            · rfl
                          · rfl
                        · rfl
  · simp [hd]
    exact star_refl _ _ _
end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Maps

theorem match_envs_set_opttemp : match_envs_set_opttempStatement := by
  intro f cenv e le m lo hi te tle tlo thi optid v tv x hme hinj hcheck
  cases optid with
  | none =>
      cases hcheck
      simpa [set_opttemp] using hme
  | some id =>
      unfold check_opttemp check_temp at hcheck
      by_cases hmem : VSet.mem id cenv = true
      · simp [hmem] at hcheck
      · simp [hmem] at hcheck
        simp only [set_opttemp]
        rcases hme with ⟨hvars, htemps, hinj_env, hrange, htrange,
          hmapped, hflat, hlo, htlo⟩
        refine ⟨?_, ?_, hinj_env, hrange, htrange, hmapped, hflat, hlo, htlo⟩
        · intro id0
          cases hvars id0 with
          | match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload htlenv hv =>
              have hne : id0 ≠ id := by
                intro heq
                subst id0
                exact hmem hlift
              exact match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload
                (by
                  have hg : PTree.get id0 (PTree.set id tv tle) = PTree.get id0 tle :=
                    PTree.gso (A := val) (i := id0) (j := id) tv tle hne
                  exact hg.trans htlenv)
                hv
          | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
              exact match_var_not_lifted b ty b' henv htenv hnlocal hmap
          | match_var_not_local henv htenv hnlocal =>
              exact match_var_not_local henv htenv hnlocal
        · intro id0 v0 hget
          change PTree.get id0 (PTree.set id v le) = some v0 at hget
          by_cases heq : id0 = id
          · subst id0
            have hs : PTree.get id (PTree.set id v le) = some v := PTree.gss id v le
            have hv0 : v = v0 := Option.some.inj (hs.symm.trans hget)
            subst v0
            refine ⟨⟨tv, PTree.gss id tv tle, hinj⟩, ?_⟩
            intro hmem'
            exact (hmem hmem').elim
          · have hget' : PTree.get id0 le = some v0 := by
              have hg : PTree.get id0 (PTree.set id v le) = PTree.get id0 le :=
                PTree.gso (A := val) (i := id0) (j := id) v le heq
              exact hg.symm.trans hget
            rcases htemps id0 v0 hget' with ⟨⟨tv0, htle, hv⟩, hcenv⟩
            refine ⟨⟨tv0, ?_, hv⟩, hcenv⟩
            change PTree.get id0 (PTree.set id tv tle) = some tv0
            have hg : PTree.get id0 (PTree.set id tv tle) = PTree.get id0 tle :=
              PTree.gso (A := val) (i := id0) (j := id) tv tle heq
            exact hg.trans htle

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Maps

theorem match_envs_change_temp : match_envs_change_tempStatement := by
  intro f cenv e le m lo hi te tle tlo thi id v hme hle hmem
  rcases hme with ⟨hvars, htemps, hinj_env, hrange, htrange,
    hmapped, hflat, hlo, htlo⟩
  refine ⟨?_, ?_, hinj_env, hrange, htrange, hmapped, hflat, hlo, htlo⟩
  · intro id0
    cases hvars id0 with
    | match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload htlenv hv =>
        have hne : id0 ≠ id := by
          intro heq
          subst id0
          have hbad : (true : Bool) = false := hlift.symm.trans hmem
          cases hbad
        exact match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload
          (by
            have hg : PTree.get id0 (PTree.set id v tle) = PTree.get id0 tle :=
              PTree.gso (A := val) (i := id0) (j := id) v tle hne
            exact hg.trans htlenv)
          hv
    | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
        exact match_var_not_lifted b ty b' henv htenv hnlocal hmap
    | match_var_not_local henv htenv hnlocal =>
        exact match_var_not_local henv htenv hnlocal
  · intro id0 v0 hget
    have hne : id0 ≠ id := by
      intro heq
      subst id0
      simpa [hle] using hget
    rcases htemps id0 v0 hget with ⟨⟨tv, htle, hv⟩, hcenv⟩
    refine ⟨⟨tv, ?_, hv⟩, hcenv⟩
    have hg : PTree.get id0 (PTree.set id v tle) = PTree.get id0 tle :=
      PTree.gso (A := val) (i := id0) (j := id) v tle hne
    exact hg.trans htle

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

theorem cenv_for_gen_domain : cenv_for_gen_domainStatement := by
  intro atk id vars
  induction vars with
  | nil =>
      intro h
      exact False.elim (VSet.MFProvider.M.empty_1 id h)
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      intro h
      change VSet.In id (add_local_variable atk (id1, ty1) (cenv_for_gen atk rest)) at h
      unfold add_local_variable at h
      cases hmode : access_mode ty1 with
      | By_value chunk =>
          by_cases hmem : VSet.mem id1 atk = true
          · simp [hmode, hmem] at h
            exact List.mem_cons.mpr (Or.inr (ih h))
          · simp [hmode, hmem] at h
            have hadd := (VSF.add_iff_proof _ id1 id).mp h
            cases hadd with
            | inl heq =>
                have : id1 = id := heq
                subst id
                exact List.mem_cons.mpr (Or.inl rfl)
            | inr hrest =>
                exact List.mem_cons.mpr (Or.inr (ih hrest))
      | By_reference =>
          simp [hmode] at h
          exact List.mem_cons.mpr (Or.inr (ih h))
      | By_copy =>
          simp [hmode] at h
          exact List.mem_cons.mpr (Or.inr (ih h))
      | By_nothing =>
          simp [hmode] at h
          exact List.mem_cons.mpr (Or.inr (ih h))

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

private theorem add_local_variable_charact_aux :
    ∀ id ty atk cenv id1,
      VSet.In id1 (add_local_variable atk (id, ty) cenv) ↔
        VSet.In id1 cenv ∨
          ∃ chunk, access_mode ty = .By_value chunk ∧ id = id1 ∧
            VSet.mem id atk = false := by
  intro id ty atk cenv id1
  unfold add_local_variable
  cases hmode : access_mode ty with
  | By_value chunk =>
      cases hmem : VSet.mem id atk with
      | false =>
          simp only [hmode, hmem, ↓reduceIte]
          constructor
          · intro h
            rcases (VSF.add_iff_proof _ id id1).mp h with heq | hrest
            · exact Or.inr ⟨chunk, rfl, heq, trivial⟩
            · exact Or.inl hrest
          · intro h
            rcases h with hrest | ⟨chunk', hmode', heq, hmem'⟩
            · exact (VSF.add_iff_proof _ id id1).mpr (Or.inr hrest)
            · exact (VSF.add_iff_proof _ id id1).mpr (Or.inl heq)
      | true =>
          simp [hmode, hmem]
  | By_reference => simp [hmode]
  | By_copy => simp [hmode]
  | By_nothing => simp [hmode]

theorem cenv_for_gen_by_value : cenv_for_gen_by_valueStatement := by
  intro atk id ty vars
  induction vars generalizing id ty with
  | nil =>
      intro hin _ _
      cases hin
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      intro hin hnr hmem
      cases hin with
      | head =>
          cases hnr with
          | cons _ hnot htail =>
              have hchar :=
                (add_local_variable_charact_aux id ty atk
                  (cenv_for_gen atk rest) id).mp hmem
              cases hchar with
              | inl hrest =>
                  have hdom : id ∈ var_names rest :=
                    cenv_for_gen_domain atk id rest hrest
                  exact False.elim (hnot hdom)
              | inr hex =>
                  rcases hex with ⟨chunk, hmode, heq, hfalse⟩
                  exact ⟨chunk, hmode⟩
      | tail _ htail =>
          cases hnr with
          | cons _ hnot hnrTail =>
              have hchar :=
                (add_local_variable_charact_aux id1 ty1 atk
                  (cenv_for_gen atk rest) id).mp hmem
              cases hchar with
              | inl hrest => exact ih id ty htail hnrTail hrest
              | inr hex =>
                  rcases hex with ⟨chunk, hmode, heq, hfalse⟩
                  have hdom : id1 ∈ var_names rest :=
                    by
                      rw [heq]
                      exact List.mem_map.mpr ⟨(id, ty), htail, rfl⟩
                  exact False.elim (hnot hdom)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

theorem cenv_for_gen_compat : cenv_for_gen_compatStatement := by
  intro atk id vars
  induction vars with
  | nil =>
      intro h
      exact False.elim (VSet.MFProvider.M.empty_1 id h)
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      intro h
      change VSet.In id (add_local_variable atk (id1, ty1) (cenv_for_gen atk rest)) at h
      unfold add_local_variable at h
      cases hmode : access_mode ty1 with
      | By_value chunk =>
          by_cases hmem : VSet.mem id1 atk = true
          · simp [hmode, hmem] at h
            exact ih h
          · simp [hmode, hmem] at h
            have hadd := (VSF.add_iff_proof _ id1 id).mp h
            cases hadd with
            | inl heq =>
                subst id
                simpa using hmem
            | inr hrest => exact ih hrest
      | By_reference =>
          simp [hmode] at h
          exact ih h
      | By_copy =>
          simp [hmode] at h
          exact ih h
      | By_nothing =>
          simp [hmode] at h
          exact ih h

theorem compat_cenv_for : compat_cenv_forStatement := by
  intro f id hatk hcenv
  have hfalse : VSet.mem id (addr_taken_stmt f.fn_body) = false := by
    apply cenv_for_gen_compat (addr_taken_stmt f.fn_body) id (f.fn_params ++ f.fn_vars)
    change VSet.In id (cenv_for_gen (addr_taken_stmt f.fn_body) (f.fn_params ++ f.fn_vars))
    exact hcenv
  have htrue : VSet.mem id (addr_taken_stmt f.fn_body) = true :=
    (VSF.mem_iff_proof _ _).mp hatk
  rw [hfalse] at htrue
  cases htrue

theorem compat_cenv_union_l : compat_cenv_union_lStatement := by
  intro atk1 atk2 cenv h
  exact compat_union_left atk1 atk2 cenv h

theorem compat_cenv_union_r : compat_cenv_union_rStatement := by
  intro atk1 atk2 cenv h
  exact compat_union_right atk1 atk2 cenv h

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals

theorem compat_cenv_empty : compat_cenv_emptyStatement := by
  intro cenv id hid hcid
  exact (VSet.MFProvider.M.empty_1 id) hid

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

private theorem alloc_nextblock_local (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hnext := congrArg Mem.nextblock hfirst
  exact hnext.symm

theorem alloc_variables_nextblock : alloc_variables_nextblockStatement := by
  intro ge e m vars e' m' halloc
  induction halloc with
  | nil =>
      exact Ple_refl _
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      apply Ple_trans _ m1.nextblock _
      · rw [alloc_nextblock_local m (.Z0 : Z) (sizeof ge.genv_cenv ty) m1 b1 halloc]
        exact Ple_succ _
      · exact ih

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_result_range_local (m : mem) (lo hi : Z) (m' : mem)
    (b : block) (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

theorem alloc_variables_range : alloc_variables_rangeStatement := by
  intro ge id b ty e m vars e' m' halloc
  induction halloc generalizing id b ty with
  | nil =>
      intro hget
      exact Or.inl hget
  | cons e m id0 ty0 vars m1 b1 m2 e2 halloc hrest ih =>
      intro hget
      have hstep := ih id b ty hget
      cases hstep with
      | inl hget1 =>
          have hspec := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
            (A := block × type) id id0 (b1, ty0) e
          rw [hspec] at hget1
          cases hp : peq id id0 with
          | left heq =>
            subst id0
            simp only [hp] at hget1
            cases hget1
            right
            constructor
            · rw [alloc_result_range_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
              exact Ple_refl _
            · exact Plt_Ple_trans b1 m1.nextblock m2.nextblock
                (by
                  rw [alloc_result_range_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
                  rw [alloc_nextblock_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
                  exact Plt_succ _)
                (alloc_variables_nextblock ge (PTree.set id (b1, ty0) e) m1 vars e2 m2 hrest)
          | right heq =>
            simp only [hp] at hget1
            exact Or.inl hget1
      | inr hrange =>
          right
          constructor
          · exact Ple_trans m.nextblock m1.nextblock b
              (by
                rw [alloc_nextblock_local m (.Z0 : Z) (sizeof ge.genv_cenv ty0) m1 b1 halloc]
                exact Ple_succ _)
              hrange.1
          · exact hrange.2

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_variables_injective_alloc_result
    (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

private theorem alloc_variables_injective_alloc_nextblock
    (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hnext := congrArg Mem.nextblock hfirst
  exact hnext.symm

theorem alloc_variables_injective : alloc_variables_injectiveStatement := by
  intro ge id1 b1 ty1 id2 b2 ty2 e m vars e' m' halloc
  induction halloc generalizing id1 b1 ty1 id2 b2 ty2 with
  | nil =>
      intro hbase hrange hget1 hget2 hids
      exact hbase hget1 hget2 hids
  | cons e m id0 ty0 vars m1 b0 m2 e2 halloc hrest ih =>
      intro hbase hrange hget1 hget2 hids
      apply ih
      · intro hj1 hj2 hjneq
        have hs1 := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := block × type) id1 id0 (b0, ty0) e
        have hs2 := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := block × type) id2 id0 (b0, ty0) e
        rw [hs1] at hj1
        rw [hs2] at hj2
        cases hp1 : peq id1 id0 with
        | left heq1 =>
          cases hp2 : peq id2 id0 with
          | left heq2 =>
            exfalso
            exact hjneq (heq1.trans heq2.symm)
          | right heq2 =>
            simp only [hp1, hp2] at hj1 hj2
            injection hj1 with hb
            have hb' : b0 = b1 := congrArg Prod.fst hb
            have hlt := hrange id2 b2 ty2 hj2
            have hne : m.nextblock ≠ b2 := by
              intro hbc
              exact (Plt_ne b2 m.nextblock hlt) hbc.symm
            intro hbc
            apply hne
            rw [← alloc_variables_injective_alloc_result m (.Z0 : Z)
              (sizeof ge.genv_cenv ty0) m1 b0 halloc]
            exact hb'.trans hbc
        | right heq1 =>
          cases hp2 : peq id2 id0 with
          | left heq2 =>
            simp only [hp1, hp2] at hj1 hj2
            injection hj2 with hb
            have hb' : b0 = b2 := congrArg Prod.fst hb
            have hlt := hrange id1 b1 ty1 hj1
            have hne : m.nextblock ≠ b1 := by
              intro hbc
              exact (Plt_ne b1 m.nextblock hlt) hbc.symm
            intro hbc
            apply hne
            rw [← alloc_variables_injective_alloc_result m (.Z0 : Z)
              (sizeof ge.genv_cenv ty0) m1 b0 halloc]
            exact hb'.trans hbc.symm
          | right heq2 =>
            simp only [hp1, hp2] at hj1 hj2
            exact hbase hj1 hj2 hjneq
      · intro j c t hj
        have hs := CompCert4Lean.Lib.Maps.PTree.gsspec_proof
          (A := block × type) j id0 (b0, ty0) e
        rw [hs] at hj
        cases hp : peq j id0 with
        | left heq =>
          simp only [hp] at hj
          cases hj
          rw [alloc_variables_injective_alloc_result m (.Z0 : Z)
            (sizeof ge.genv_cenv ty0) m1 b0 halloc]
          rw [alloc_variables_injective_alloc_nextblock m (.Z0 : Z)
            (sizeof ge.genv_cenv ty0) m1 b0 halloc]
          exact Plt_succ _
        | right heq =>
          simp only [hp] at hj
          exact Plt_trans c m.nextblock m1.nextblock (hrange j c t hj)
            (by
              rw [alloc_variables_injective_alloc_nextblock m (.Z0 : Z)
                (sizeof ge.genv_cenv ty0) m1 b0 halloc]
              exact Plt_succ _)
      · exact hget1
      · exact hget2
      · exact hids

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem mav_alloc_result (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : b = m.nextblock := by
  unfold Mem.alloc at halloc
  exact (congrArg Prod.snd halloc).symm

private theorem mav_alloc_nextblock (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) :
    m'.nextblock = PArith.BinPos.Pos.succ m.nextblock := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  exact (congrArg Mem.nextblock hfirst).symm

private theorem mav_alloc_valid_old (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hvalid : Mem.valid_block m b') :
    Mem.valid_block m' b' := by
  unfold Mem.valid_block at hvalid ⊢
  rw [mav_alloc_nextblock m lo hi m' b halloc]
  exact Plt_trans_succ _ _ hvalid

private theorem mav_alloc_fresh_invalid (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : ¬ Mem.valid_block m b := by
  rw [mav_alloc_result m lo hi m' b halloc]
  exact Plt_strict _

private theorem mav_alloc_fresh_valid (m : mem) (lo hi : Z) (m' : mem) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) : Mem.valid_block m' b := by
  unfold Mem.valid_block
  rw [mav_alloc_result m lo hi m' b halloc]
  rw [mav_alloc_nextblock m lo hi m' b halloc]
  exact Plt_succ _

private theorem mav_alloc_valid_inv (m : mem) (lo hi : Z) (m' : mem) (b x : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hvalid : Mem.valid_block m' x) :
    x = b ∨ Mem.valid_block m x := by
  have hlt : Plt x (PArith.BinPos.Pos.succ m.nextblock) := by
    unfold Mem.valid_block at hvalid
    rwa [mav_alloc_nextblock m lo hi m' b halloc] at hvalid
  have hle : PArith.BinPos.Pos.le x m.nextblock :=
    (PArith.BinPos.Pos.lt_succ_r x m.nextblock).mp hlt
  by_cases hx : x = b
  · exact Or.inl hx
  · right
    unfold Mem.valid_block Plt
    change posToNat x < posToNat m.nextblock
    change posToNat x ≤ posToNat m.nextblock at hle
    have hne : posToNat x ≠ posToNat m.nextblock := by
      intro heq
      apply hx
      rw [mav_alloc_result m lo hi m' b halloc]
      exact posToNat_injective heq
    omega

private theorem mav_alloc_access_old (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hne : b' ≠ b) :
    PMap.get b' m'.mem_access = PMap.get b' m.mem_access := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have haccess := congrArg (fun x : mem => x.mem_access) hfirst
  rw [← haccess]
  apply PMap.gso
  rwa [mav_alloc_result m lo hi m' b halloc] at hne

private theorem mav_alloc_contents_old (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hne : b' ≠ b) :
    PMap.get b' m'.mem_contents = PMap.get b' m.mem_contents := by
  unfold Mem.alloc at halloc
  have hfirst := congrArg Prod.fst halloc
  have hcontents := congrArg (fun x : mem => x.mem_contents) hfirst
  rw [← hcontents]
  apply PMap.gso
  rwa [mav_alloc_result m lo hi m' b halloc] at hne

private theorem mav_alloc_perm_old_iff (m : mem) (lo hi : Z) (m' : mem) (b b' : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (hne : b' ≠ b)
    (ofs : Z) (k : perm_kind) (p : permission) :
    Mem.perm m' b' ofs k p ↔ Mem.perm m b' ofs k p := by
  unfold Mem.perm
  rw [mav_alloc_access_old m lo hi m' b b' halloc hne]

private theorem mav_alloc_new_perm_transfer
    (m tm m' tm' : mem) (lo hi : Z) (b tb : block)
    (halloc : Mem.alloc m lo hi = (m', b))
    (htalloc : Mem.alloc tm lo hi = (tm', tb))
    (ofs : Z) (k : perm_kind) (p : permission) :
    Mem.perm m' b ofs k p → Mem.perm tm' tb ofs k p := by
  intro hperm
  unfold Mem.alloc at halloc htalloc
  cases halloc
  cases htalloc
  unfold Mem.perm at hperm ⊢
  rw [PMap.gss] at hperm ⊢
  exact hperm

private theorem mav_alloc_new_contents_undef
    (m m' : mem) (lo hi : Z) (b : block)
    (halloc : Mem.alloc m lo hi = (m', b)) (ofs : Z) :
    ZMap.get ofs (PMap.get b m'.mem_contents) = Undef := by
  unfold Mem.alloc at halloc
  cases halloc
  rw [PMap.gss]
  exact ZMap.gi_proof _ _ _

private theorem mav_alloc_left_unmapped
    (f : meminj) (m tm m' : mem) (lo hi : Z) (b : block)
    (hinj : Mem.inject f m tm) (halloc : Mem.alloc m lo hi = (m', b)) :
    ∃ f', Mem.inject f' m' tm ∧ inject_incr f f' ∧ f' b = none ∧
      ∀ x, x ≠ b → f' x = f x := by
  let f' : meminj := fun x => if x = b then none else f x
  have hfb : f b = none := hinj.mi_freeblocks b
    (mav_alloc_fresh_invalid m lo hi m' b halloc)
  have hincr : inject_incr f f' := by
    intro x x' delta hmap
    by_cases hx : x = b
    · subst x
      rw [hfb] at hmap
      cases hmap
    · simpa [f', hx] using hmap
  refine ⟨f', ?_, hincr, by simp [f'], ?_⟩
  · refine {
      mi_inj := ?_,
      mi_freeblocks := ?_,
      mi_mappedblocks := ?_,
      mi_no_overlap := ?_,
      mi_representable := ?_,
      mi_perm_inv := ?_ }
    · refine {
        mi_perm := ?_,
        mi_align := ?_,
        mi_memval := ?_ }
      · intro x x' delta ofs k p hmap hperm
        have hx : x ≠ b := by
          intro heq
          subst x
          simp [f'] at hmap
        have hmap0 : f x = some (x', delta) := by simpa [f', hx] using hmap
        exact hinj.mi_inj.mi_perm x x' delta ofs k p hmap0
          ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mp hperm)
      · intro x x' delta chunk ofs p hmap hrange
        have hx : x ≠ b := by
          intro heq
          subst x
          simp [f'] at hmap
        have hmap0 : f x = some (x', delta) := by simpa [f', hx] using hmap
        apply hinj.mi_inj.mi_align x x' delta chunk ofs p hmap0
        intro q hq
        exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx q Max p).mp
          (hrange q hq)
      · intro x ofs x' delta hmap hperm
        have hx : x ≠ b := by
          intro heq
          subst x
          simp [f'] at hmap
        have hmap0 : f x = some (x', delta) := by simpa [f', hx] using hmap
        rw [mav_alloc_contents_old m lo hi m' b x halloc hx]
        exact CompCert4Lean.Common.Memdata.memval_inject_incr f f' _ _
          (hinj.mi_inj.mi_memval x ofs x' delta hmap0
            ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Cur Readable).mp hperm))
          hincr
    · intro x hinvalid
      by_cases hx : x = b
      · simp [f', hx]
      · have hinvalid0 : ¬ Mem.valid_block m x := by
          intro hvalid
          exact hinvalid (mav_alloc_valid_old m lo hi m' b x halloc hvalid)
        dsimp [f']
        split
        · rename_i heq
          exact False.elim (hx heq)
        · exact hinj.mi_freeblocks x hinvalid0
    · intro x x' delta hmap
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      exact hinj.mi_mappedblocks x x' delta (by simpa [f', hx] using hmap)
    · intro x x' delta y y' delta' ofs ofs' hxy hmap hmap' hperm hperm'
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      have hy : y ≠ b := by
        intro heq
        subst y
        simp [f'] at hmap'
      apply hinj.mi_no_overlap x x' delta y y' delta' ofs ofs' hxy
        (by simpa [f', hx] using hmap) (by simpa [f', hy] using hmap')
      · exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Max Nonempty).mp hperm
      · exact (mav_alloc_perm_old_iff m lo hi m' b y halloc hy ofs' Max Nonempty).mp hperm'
    · intro x x' delta ofs hmap hperm
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      apply hinj.mi_representable x x' delta ofs (by simpa [f', hx] using hmap)
      cases hperm with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (Ptrofs.unsigned ofs) Max Nonempty).mp hp)
      | inr hp =>
          exact Or.inr ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (.Zpos .xH)) Max Nonempty).mp hp)
    · intro x ofs x' delta k p hmap hperm
      have hx : x ≠ b := by
        intro heq
        subst x
        simp [f'] at hmap
      have hbase := hinj.mi_perm_inv x ofs x' delta k p
        (by simpa [f', hx] using hmap) hperm
      cases hbase with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mpr hp)
      | inr hp =>
          exact Or.inr (by
            intro hp'
            exact hp ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
              ofs Max Nonempty).mp hp'))
  · intro x hx
    simp [f', hx]

private theorem mav_zdivide_zero (a : Z) : ZArith.BinInt.Z.divide a (.Z0 : Z) := by
  refine ⟨.Z0, ?_⟩
  apply intOfZ_injective
  change intOfZ (.Z0 : Z) = intOfZ (zOfInt (intOfZ a * intOfZ (.Z0 : Z)))
  rw [intOfZ_zOfInt]
  change 0 = intOfZ a * 0
  omega

private theorem mav_zadd_zero (a : Z) : ZArith.BinInt.Z.add a (.Z0 : Z) = a := by
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  change intOfZ a + 0 = intOfZ a
  omega

private theorem mav_ptrofs_unsigned_range (i : Ptrofs.int) :
    ZArith.BinInt.Z.le (.Z0 : Z) (Ptrofs.unsigned i) ∧
      ZArith.BinInt.Z.le (Ptrofs.unsigned i) Ptrofs.max_unsigned := by
  constructor
  · have h := i.intrange.1
    change (-1 : _root_.Int) < intOfZ i.intval at h
    change 0 ≤ intOfZ i.intval
    omega
  · have h := i.intrange.2
    change intOfZ i.intval < intOfZ Ptrofs.modulus at h
    change intOfZ i.intval ≤
      intOfZ (ZArith.BinInt.Z.sub Ptrofs.modulus (.Zpos .xH))
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    change intOfZ i.intval ≤ intOfZ Ptrofs.modulus - 1
    omega

private theorem mav_alloc_parallel_same
    (f : meminj) (m tm m' tm' : mem) (lo hi : Z) (b tb : block)
    (hinj : Mem.inject f m tm)
    (halloc : Mem.alloc m lo hi = (m', b))
    (htalloc : Mem.alloc tm lo hi = (tm', tb)) :
    ∃ f', Mem.inject f' m' tm' ∧ inject_incr f f' ∧
      f' b = some (tb, (.Z0 : Z)) ∧ ∀ x, x ≠ b → f' x = f x := by
  let f' : meminj := fun x => if x = b then some (tb, (.Z0 : Z)) else f x
  have hfb : f b = none := hinj.mi_freeblocks b
    (mav_alloc_fresh_invalid m lo hi m' b halloc)
  have hincr : inject_incr f f' := by
    intro x x' delta hmap
    by_cases hx : x = b
    · subst x
      rw [hfb] at hmap
      cases hmap
    · simpa [f', hx] using hmap
  have hnew : f' b = some (tb, (.Z0 : Z)) := by simp [f']
  have hold : ∀ x, x ≠ b → f' x = f x := by
    intro x hx
    simp [f', hx]
  refine ⟨f', ?_, hincr, hnew, hold⟩
  refine {
    mi_inj := ?_,
    mi_freeblocks := ?_,
    mi_mappedblocks := ?_,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · refine {
      mi_perm := ?_,
      mi_align := ?_,
      mi_memval := ?_ }
    · intro x x' delta ofs k p hmap hperm
      by_cases hx : x = b
      · subst x
        rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        subst delta
        change Mem.perm tm' (show positive from tb)
          (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p
        rw [mav_zadd_zero]
        exact mav_alloc_new_perm_transfer m tm m' tm' lo hi b tb
          halloc htalloc ofs k p hperm
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        have hx'valid := hinj.mi_mappedblocks x x' delta hmap0
        have hx' : x' ≠ tb := by
          rw [mav_alloc_result tm lo hi tm' tb htalloc]
          exact Plt_ne x' tm.nextblock hx'valid
        exact (mav_alloc_perm_old_iff tm lo hi tm' tb x' htalloc hx'
          (ZArith.BinInt.Z.add ofs delta) k p).mpr
            (hinj.mi_inj.mi_perm x x' delta ofs k p hmap0
              ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mp hperm))
    · intro x x' delta chunk ofs p hmap hrange
      by_cases hx : x = b
      · subst x
        rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        subst delta
        exact mav_zdivide_zero _
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        apply hinj.mi_inj.mi_align x x' delta chunk ofs p hmap0
        intro q hq
        exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx q Max p).mp
          (hrange q hq)
    · intro x ofs x' delta hmap hperm
      by_cases hx : x = b
      · subst x
        rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        subst delta
        rw [mav_alloc_new_contents_undef m m' lo hi b halloc ofs]
        exact memval_inject.undef f' _
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        have hx'valid := hinj.mi_mappedblocks x x' delta hmap0
        have hx' : x' ≠ tb := by
          rw [mav_alloc_result tm lo hi tm' tb htalloc]
          exact Plt_ne x' tm.nextblock hx'valid
        rw [mav_alloc_contents_old m lo hi m' b x halloc hx]
        rw [mav_alloc_contents_old tm lo hi tm' tb x' htalloc hx']
        exact CompCert4Lean.Common.Memdata.memval_inject_incr f f' _ _
          (hinj.mi_inj.mi_memval x ofs x' delta hmap0
            ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Cur Readable).mp hperm))
          hincr
  · intro x hinvalid
    by_cases hx : x = b
    · subst x
      exact False.elim (hinvalid (mav_alloc_fresh_valid m lo hi m' b halloc))
    · have hinvalid0 : ¬ Mem.valid_block m x := by
        intro hvalid
        exact hinvalid (mav_alloc_valid_old m lo hi m' b x halloc hvalid)
      rw [hold x hx]
      exact hinj.mi_freeblocks x hinvalid0
  · intro x x' delta hmap
    by_cases hx : x = b
    · subst x
      rw [hnew] at hmap
      have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
      have hxb : tb = x' := congrArg Prod.fst hpair
      have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
      subst x'
      exact mav_alloc_fresh_valid tm lo hi tm' tb htalloc
    · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
      exact mav_alloc_valid_old tm lo hi tm' tb x' htalloc
        (hinj.mi_mappedblocks x x' delta hmap0)
  · intro x x' delta y y' delta' ofs ofs' hxy hmap hmap' hperm hperm'
    by_cases hx : x = b
    · subst x
      by_cases hy : y = b
      · exact False.elim (hxy hy.symm)
      · rw [hnew] at hmap
        have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
        have hxb : tb = x' := congrArg Prod.fst hpair
        have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
        subst x'
        have hmap0 : f y = some (y', delta') := by simpa [hold y hy] using hmap'
        left
        intro heq
        have hyvalid := hinj.mi_mappedblocks y y' delta' hmap0
        have hyne : y' ≠ tb := by
          rw [mav_alloc_result tm lo hi tm' tb htalloc]
          exact Plt_ne y' tm.nextblock hyvalid
        exact hyne heq.symm
    · by_cases hy : y = b
      · subst y
        rw [hnew] at hmap'
        have hpair : (tb, (.Z0 : Z)) = (y', delta') := Option.some.inj hmap'
        have hyb : tb = y' := congrArg Prod.fst hpair
        have hdelta' : (.Z0 : Z) = delta' := congrArg Prod.snd hpair
        subst y'
        have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        left
        have hxvalid := hinj.mi_mappedblocks x x' delta hmap0
        rw [mav_alloc_result tm lo hi tm' tb htalloc]
        exact Plt_ne x' tm.nextblock hxvalid
      · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
        have hmap0' : f y = some (y', delta') := by simpa [hold y hy] using hmap'
        apply hinj.mi_no_overlap x x' delta y y' delta' ofs ofs' hxy hmap0 hmap0'
        · exact (mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs Max Nonempty).mp hperm
        · exact (mav_alloc_perm_old_iff m lo hi m' b y halloc hy ofs' Max Nonempty).mp hperm'
  · intro x x' delta ofs hmap hperm
    by_cases hx : x = b
    · subst x
      rw [hnew] at hmap
      have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
      have hxb : tb = x' := congrArg Prod.fst hpair
      have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
      subst x'
      subst delta
      have hrange := mav_ptrofs_unsigned_range ofs
      have hz : ZArith.BinInt.Z.le (.Z0 : Z) .Z0 := by
        change (0 : _root_.Int) ≤ 0
        omega
      change ZArith.BinInt.Z.le (.Z0 : Z) .Z0 ∧
        ZArith.BinInt.Z.le (.Z0 : Z)
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (.Z0 : Z)) ∧
        ZArith.BinInt.Z.le
          (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) (.Z0 : Z)) Ptrofs.max_unsigned
      rw [mav_zadd_zero]
      exact And.intro hz hrange
    · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
      apply hinj.mi_representable x x' delta ofs hmap0
      cases hperm with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (Ptrofs.unsigned ofs) Max Nonempty).mp hp)
      | inr hp =>
          exact Or.inr ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
            (ZArith.BinInt.Z.sub (Ptrofs.unsigned ofs) (.Zpos .xH)) Max Nonempty).mp hp)
  · intro x ofs x' delta k p hmap hperm
    by_cases hx : x = b
    · subst x
      rw [hnew] at hmap
      have hpair : (tb, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap
      have hxb : tb = x' := congrArg Prod.fst hpair
      have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hpair
      subst x'
      subst delta
      exact Or.inl (by
        change Mem.perm tm' (show positive from tb)
          (ZArith.BinInt.Z.add ofs (.Z0 : Z)) k p at hperm
        rw [mav_zadd_zero] at hperm
        exact mav_alloc_new_perm_transfer tm m tm' m' lo hi tb b
          htalloc halloc ofs k p hperm)
    · have hmap0 : f x = some (x', delta) := by simpa [hold x hx] using hmap
      have hx'valid := hinj.mi_mappedblocks x x' delta hmap0
      have hx' : x' ≠ tb := by
        rw [mav_alloc_result tm lo hi tm' tb htalloc]
        exact Plt_ne x' tm.nextblock hx'valid
      have hbase := hinj.mi_perm_inv x ofs x' delta k p hmap0
        ((mav_alloc_perm_old_iff tm lo hi tm' tb x' htalloc hx'
          (ZArith.BinInt.Z.add ofs delta) k p).mp hperm)
      cases hbase with
      | inl hp =>
          exact Or.inl ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx ofs k p).mpr hp)
      | inr hp =>
          exact Or.inr (by
            intro hp'
            exact hp ((mav_alloc_perm_old_iff m lo hi m' b x halloc hx
              ofs Max Nonempty).mp hp'))

theorem match_alloc_variables : match_alloc_variablesStatement := by
  unfold match_alloc_variablesStatement
  intro cfg p tp hprog
  dsimp only
  intro cenv e m vars e' m' halloc j tm te hnorep hinj
  have hcenv : (globalenv tp).genv_cenv = (globalenv p).genv_cenv :=
    comp_env_preserved cfg p tp hprog
  induction halloc generalizing j tm te with
  | nil =>
      refine ⟨j, te, tm, alloc_variables.nil te tm, hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro b b' delta hmap
        exact hmap
      · intro b _
        rfl
      · intro b b' delta _ _
        rfl
      · intro b b' delta hmap hnot
        exact False.elim (hnot (hinj.mi_mappedblocks b b' delta hmap))
      · intro id ty hmem
        cases hmem
      · intro id _
        exact ⟨rfl, rfl⟩
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      change list_norepet (id :: var_names vars) at hnorep
      cases hnorep with
      | cons _ hnotid hnrtail =>
        by_cases hmem : VSet.mem id cenv = true
        · rcases mav_alloc_left_unmapped j m tm m1 (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) b1 hinj halloc with
            ⟨j1, hinj1, hincr1, hj1new, hj1same⟩
          rcases ih j1 tm te hnrtail hinj1 with
            ⟨j', te', tm', htalloc, hinj', hincr', hsrc, htgt, hnew, hvars, hout⟩
          have htalloc' : alloc_variables (globalenv tp) te tm
              (remove_lifted cenv ((id, ty) :: vars)) te' tm' := by
            simpa [remove_lifted, hmem] using htalloc
          refine ⟨j', te', tm', htalloc', hinj', ?_, ?_, ?_, hnew, ?_, ?_⟩
          · intro x x' delta hmap
            exact hincr' x x' delta (hincr1 x x' delta hmap)
          · intro x hvalid
            have hx : x ≠ b1 := by
              intro heq
              subst x
              exact (mav_alloc_fresh_invalid m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc) hvalid
            calc
              j' x = j1 x := hsrc x (mav_alloc_valid_old m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 x halloc hvalid)
              _ = j x := hj1same x hx
          · intro x x' delta hmap hvalid
            have hj : j' x = j1 x := htgt x x' delta hmap hvalid
            have hmap1 : j1 x = some (x', delta) := by simpa [← hj] using hmap
            have hx : x ≠ b1 := by
              intro heq
              subst x
              rw [hj1new] at hmap1
              cases hmap1
            exact hj.trans (hj1same x hx)
          · intro id0 ty0 hpair
            simp only [List.mem_cons] at hpair
            cases hpair with
            | inl heq =>
                cases heq
                have ho := hout id hnotid
                refine ⟨b1, ?_, ?_⟩
                · calc
                    PTree.get id e2 = PTree.get id (PTree.set id (b1, ty) e) := ho.1
                    _ = some (b1, ty) := PTree.gss (A := block × type) id (b1, ty) e
                · simp only [hmem, if_true]
                  exact ⟨ho.2, (hsrc b1 (mav_alloc_fresh_valid m (.Z0 : Z)
                    (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc)).trans hj1new⟩
            | inr htail => exact hvars id0 ty0 htail
          · intro id0 hall
            change id0 ∉ id :: var_names vars at hall
            have hid : id0 ≠ id := by
              intro heq
              apply hall
              simp [heq]
            have htail : id0 ∉ var_names vars := by
              intro h
              exact hall (List.mem_cons_of_mem id h)
            have ho := hout id0 htail
            constructor
            · calc
                PTree.get id0 e2 = PTree.get id0 (PTree.set id (b1, ty) e) := ho.1
                _ = PTree.get id0 e := PTree.gso (A := block × type) (b1, ty) e hid
            · exact ho.2
        · rcases htm : Mem.alloc tm (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) with ⟨tm1, tb1⟩
          have htallocSource : Mem.alloc tm (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) = (tm1, tb1) := htm
          have htallocTarget : Mem.alloc tm (.Z0 : Z)
              (sizeof (globalenv tp).genv_cenv ty) = (tm1, tb1) := by
            rw [hcenv]
            exact htallocSource
          rcases mav_alloc_parallel_same j m tm m1 tm1 (.Z0 : Z)
              (sizeof (globalenv p).genv_cenv ty) b1 tb1 hinj halloc htallocSource with
            ⟨j1, hinj1, hincr1, hj1new, hj1same⟩
          rcases ih j1 tm1 (PTree.set id (tb1, ty) te) hnrtail hinj1 with
            ⟨j', te', tm', htrest, hinj', hincr', hsrc, htgt, hnew, hvars, hout⟩
          have htcons : alloc_variables (globalenv tp) te tm ((id, ty) ::
              remove_lifted cenv vars) te' tm' :=
            alloc_variables.cons te tm id ty (remove_lifted cenv vars) tm1 tb1 tm' te'
              htallocTarget htrest
          have htalloc' : alloc_variables (globalenv tp) te tm
              (remove_lifted cenv ((id, ty) :: vars)) te' tm' := by
            simpa [remove_lifted, hmem] using htcons
          refine ⟨j', te', tm', htalloc', hinj', ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro x x' delta hmap
            exact hincr' x x' delta (hincr1 x x' delta hmap)
          · intro x hvalid
            have hx : x ≠ b1 := by
              intro heq
              subst x
              exact (mav_alloc_fresh_invalid m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc) hvalid
            calc
              j' x = j1 x := hsrc x (mav_alloc_valid_old m (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) m1 b1 x halloc hvalid)
              _ = j x := hj1same x hx
          · intro x x' delta hmap hvalid
            have hj : j' x = j1 x := htgt x x' delta hmap
              (mav_alloc_valid_old tm (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) tm1 tb1 x' htallocSource hvalid)
            have hmap1 : j1 x = some (x', delta) := by simpa [← hj] using hmap
            have hx : x ≠ b1 := by
              intro heq
              subst x
              rw [hj1new] at hmap1
              have hp : (tb1, (.Z0 : Z)) = (x', delta) := Option.some.inj hmap1
              have hb : tb1 = x' := congrArg Prod.fst hp
              subst x'
              exact (mav_alloc_fresh_invalid tm (.Z0 : Z)
                (sizeof (globalenv p).genv_cenv ty) tm1 tb1 htallocSource) hvalid
            exact hj.trans (hj1same x hx)
          · intro x x' delta hmap hnot
            by_cases hxb : x' = tb1
            · subst x'
              have hj : j' x = j1 x := htgt x tb1 delta hmap
                (mav_alloc_fresh_valid tm (.Z0 : Z)
                  (sizeof (globalenv p).genv_cenv ty) tm1 tb1 htallocSource)
              have hmap1 : j1 x = some (tb1, delta) := hj.symm.trans hmap
              by_cases hx : x = b1
              · subst x
                rw [hj1new] at hmap1
                have hp : (tb1, (.Z0 : Z)) = (tb1, delta) := Option.some.inj hmap1
                have hdelta : (.Z0 : Z) = delta := congrArg Prod.snd hp
                subst delta
                have ho := hout id hnotid
                refine ⟨id, ty, ?_, ?_, rfl⟩
                · calc
                    PTree.get id e2 = PTree.get id (PTree.set id (b1, ty) e) := ho.1
                    _ = some (b1, ty) := PTree.gss (A := block × type) id (b1, ty) e
                · rw [ho.2]
                  exact PTree.gss (A := block × type) id (tb1, ty) te
              · rw [hj1same x hx] at hmap1
                exact False.elim (hnot (hinj.mi_mappedblocks x tb1 delta hmap1))
            · apply hnew x x' delta hmap
              intro hvalid1
              cases mav_alloc_valid_inv tm (.Z0 : Z)
                  (sizeof (globalenv p).genv_cenv ty) tm1 tb1 x'
                  htallocSource hvalid1 with
              | inl heq => exact hxb heq
              | inr hvalid0 => exact hnot hvalid0
          · intro id0 ty0 hpair
            simp only [List.mem_cons] at hpair
            cases hpair with
            | inl heq =>
                cases heq
                have ho := hout id hnotid
                refine ⟨b1, ?_, ?_⟩
                · calc
                    PTree.get id e2 = PTree.get id (PTree.set id (b1, ty) e) := ho.1
                    _ = some (b1, ty) := PTree.gss (A := block × type) id (b1, ty) e
                · simp only [hmem, if_false]
                  refine ⟨tb1, ?_, ?_⟩
                  · rw [ho.2]
                    exact PTree.gss (A := block × type) id (tb1, ty) te
                  · exact (hsrc b1 (mav_alloc_fresh_valid m (.Z0 : Z)
                    (sizeof (globalenv p).genv_cenv ty) m1 b1 halloc)).trans hj1new
            | inr htail =>
                have hid : id0 ≠ id := by
                  intro heq
                  subst id0
                  apply hnotid
                  change id ∈ var_names vars
                  exact List.mem_map.mpr ⟨(id, ty0), htail, rfl⟩
                have hv := hvars id0 ty0 htail
                rcases hv with ⟨b, hb, hv⟩
                refine ⟨b, hb, ?_⟩
                cases hm0 : VSet.mem id0 cenv with
                | false => simpa [hm0] using hv
                | true =>
                    simp only [hm0, if_true] at hv ⊢
                    exact ⟨hv.1.trans (PTree.gso (A := block × type)
                      (tb1, ty) te hid), hv.2⟩
          · intro id0 hall
            change id0 ∉ id :: var_names vars at hall
            have hid : id0 ≠ id := by
              intro heq
              apply hall
              simp [heq]
            have htail : id0 ∉ var_names vars := by
              intro h
              exact hall (List.mem_cons_of_mem id h)
            have ho := hout id0 htail
            constructor
            · calc
                PTree.get id0 e2 = PTree.get id0 (PTree.set id (b1, ty) e) := ho.1
                _ = PTree.get id0 e := PTree.gso (A := block × type) (b1, ty) e hid
            · rw [ho.2]
              exact PTree.gso (A := block × type) (tb1, ty) te hid

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_variables_load_alloc_local
    (m : mem) (lo hi : Z) (m' : mem) (fresh : block)
    (halloc : Mem.alloc m lo hi = (m', fresh))
    (chunk : memory_chunk) (b : block) (ofs : Z) (v : val)
    (hload : Mem.load chunk m b ofs = some v) :
    Mem.load chunk m' b ofs = some v := by
  have hvacc := Mem.load_valid_access m chunk b ofs v hload
  have hperm : Mem.perm m b ofs Cur Readable := by
    apply hvacc.1 ofs
    constructor
    · change intOfZ ofs ≤ intOfZ ofs
      omega
    · change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add ofs (size_chunk chunk))
      have hsize := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
      change 0 < intOfZ (size_chunk chunk) at hsize
      unfold ZArith.BinInt.Z.add
      rw [intOfZ_zOfInt]
      omega
  have hvalid := Mem.perm_valid_block m b ofs Cur Readable hperm
  have hfresh : fresh = m.nextblock := by
    unfold Mem.alloc at halloc
    exact (congrArg Prod.snd halloc).symm
  have hne : b ≠ fresh := by
    rw [hfresh]
    exact Plt_ne b m.nextblock hvalid
  have haccess : PMap.get b m'.mem_access = PMap.get b m.mem_access := by
    unfold Mem.alloc at halloc
    have hfirst := congrArg Prod.fst halloc
    have heq := congrArg (fun x : mem => x.mem_access) hfirst
    rw [← heq]
    apply PMap.gso
    rwa [hfresh] at hne
  have hcontents : PMap.get b m'.mem_contents = PMap.get b m.mem_contents := by
    unfold Mem.alloc at halloc
    have hfirst := congrArg Prod.fst halloc
    have heq := congrArg (fun x : mem => x.mem_contents) hfirst
    rw [← heq]
    apply PMap.gso
    rwa [hfresh] at hne
  have hvacc' : Mem.valid_access m' chunk b ofs Readable := by
    constructor
    · intro q hq
      unfold Mem.perm
      rw [haccess]
      exact hvacc.1 q hq
    · exact hvacc.2
  rcases Mem.valid_access_load m' chunk b ofs hvacc' with ⟨v', hload'⟩
  have hres' := Mem.load_result chunk m' b ofs v' hload'
  have hres := Mem.load_result chunk m b ofs v hload
  have hv : v' = v := by
    calc
      v' = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m'.mem_contents)) := hres'
      _ = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b m.mem_contents)) := by rw [hcontents]
      _ = v := hres.symm
  simpa [hv] using hload'

theorem alloc_variables_load : alloc_variables_loadStatement := by
  intro prog e m vars e' m' halloc
  induction halloc with
  | nil =>
      intro chunk b ofs v hload
      exact hload
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      intro chunk b ofs v hload
      apply ih
      exact alloc_variables_load_alloc_local m (.Z0 : Z)
        (sizeof (globalenv prog).genv_cenv ty) m1 b1 halloc chunk b ofs v hload

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem sizeof_by_value : sizeof_by_valueStatement := by
  intro prog ty chunk hmode
  cases ty with
  | Tvoid => cases hmode
  | Tint sz sg a =>
      cases sz <;> cases sg <;> cases hmode <;>
        simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
          CompCert4Lean.Common.Memdata.size_chunk,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tlong sg a =>
      cases hmode
      simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
        CompCert4Lean.Common.Memdata.size_chunk,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tfloat sz a =>
      cases sz <;> cases hmode <;>
        simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
          CompCert4Lean.Common.Memdata.size_chunk,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tpointer t a =>
      cases hmode
      simp [CompCert4Lean.Cfrontend.Ctypes.sizeof,
        CompCert4Lean.Common.Memdata.size_chunk,
        CompCert4Lean.Common.AST.Mptr,
        CompCert4Lean.X86_64.Archi.ptr64,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le]
  | Tarray t n a => cases hmode
  | Tfunction args ret cc => cases hmode
  | Tstruct id a => cases hmode
  | Tunion id a => cases hmode

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem alloc_variables_initial_value_fresh
    (prog : program) (m m' : mem) (b : block) (ty : type)
    (halloc : Mem.alloc m (.Z0 : Z) (sizeof (globalenv prog).genv_cenv ty) = (m', b))
    (chunk : memory_chunk) (hmode : access_mode ty = .By_value chunk) :
    Mem.load chunk m' b (.Z0 : Z) = some .Vundef := by
  have hsize := sizeof_by_value prog ty chunk hmode
  have hvacc : Mem.valid_access m' chunk b (.Z0 : Z) Readable := by
    constructor
    · intro ofs hof
      have hlo := hof.1
      have hhi := hof.2
      have hbound : ZArith.BinInt.Z.lt ofs (sizeof (globalenv prog).genv_cenv ty) := by
        change 0 ≤ intOfZ ofs at hlo
        change intOfZ ofs < intOfZ (ZArith.BinInt.Z.add (.Z0 : Z) (size_chunk chunk)) at hhi
        change intOfZ (size_chunk chunk) ≤
          intOfZ (sizeof (globalenv prog).genv_cenv ty) at hsize
        unfold ZArith.BinInt.Z.add at hhi
        rw [intOfZ_zOfInt] at hhi
        have hz : intOfZ (.Z0 : Z) = 0 := rfl
        rw [hz] at hhi
        change intOfZ ofs < intOfZ (sizeof (globalenv prog).genv_cenv ty)
        omega
      unfold Mem.perm
      unfold Mem.alloc at halloc
      cases halloc
      rw [PMap.gss]
      change Mem.perm_order'
        (if (ZArith.BinInt.Z.leb (.Z0 : Z) ofs &&
          ZArith.BinInt.Z.ltb ofs (sizeof (globalenv prog).genv_cenv ty)) = true
          then some Freeable else none) Readable
      have hin : (ZArith.BinInt.Z.leb (.Z0 : Z) ofs &&
          ZArith.BinInt.Z.ltb ofs (sizeof (globalenv prog).genv_cenv ty)) = true := by
        change intOfZ (.Z0 : Z) ≤ intOfZ ofs at hlo
        change intOfZ ofs < intOfZ (sizeof (globalenv prog).genv_cenv ty) at hbound
        simpa [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb] using And.intro hlo hbound
      rw [if_pos hin]
      exact perm_F_any Readable
    · exact mav_zdivide_zero _
  rcases Mem.valid_access_load m' chunk b (.Z0 : Z) hvacc with ⟨v, hload⟩
  have hres := Mem.load_result chunk m' b (.Z0 : Z) v hload
  have hhead := mav_alloc_new_contents_undef m m' (.Z0 : Z)
    (sizeof (globalenv prog).genv_cenv ty) b halloc (.Z0 : Z)
  have hdecode : decode_val chunk
      (Mem.getN (size_chunk_nat chunk) (.Z0 : Z) (PMap.get b m'.mem_contents)) =
      Vundef := by
    obtain ⟨n, hn⟩ := size_chunk_nat_pos chunk
    rw [hn]
    simpa only [Mem.getN, hhead] using
      (decode_val_undef
        (Mem.getN n (ZArith.BinInt.Z.add (.Z0 : Z) (.Zpos .xH))
          (PMap.get b m'.mem_contents)) chunk)
  have hv : v = Vundef := hres.trans hdecode
  simpa [hv] using hload

theorem alloc_variables_initial_value : alloc_variables_initial_valueStatement := by
  intro prog e m vars e' m' halloc hinit
  induction halloc with
  | nil => exact hinit
  | cons e m id ty vars m1 b1 m2 e2 halloc hrest ih =>
      apply ih
      intro id' b ty' chunk hget hmode
      have hspec := PTree.gsspec_proof (A := block × type)
        id' id (b1, ty) e
      rw [hspec] at hget
      cases hid : peq id' id with
      | left heq =>
          simp only [hid] at hget
          cases hget
          exact alloc_variables_initial_value_fresh prog m m1 b1 ty halloc chunk hmode
      | right hne =>
          simp only [hid] at hget
          exact alloc_variables_load_alloc_local m (.Z0 : Z)
            (sizeof (globalenv prog).genv_cenv ty) m1 b1 halloc chunk b (.Z0 : Z)
            Vundef (hinit id' b ty' chunk hget hmode)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Maps

theorem create_undef_temps_charact : create_undef_temps_charactStatement := by
  intro id ty vars hmem
  induction vars with
  | nil => cases hmem
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      cases hmem with
      | head _ =>
          simpa [create_undef_temps] using
            (PTree.gss (A := CompCert4Lean.Common.Values.val) id
              (.Vundef) (create_undef_temps rest))
      | tail _ htail =>
          by_cases hne : id ≠ id1
          · have hget := PTree.gso (A := CompCert4Lean.Common.Values.val)
                (i := id) (j := id1)
                (.Vundef) (create_undef_temps rest) hne
            change PTree.get id
              (PTree.set id1 (.Vundef) (create_undef_temps rest)) =
              some .Vundef
            exact hget.trans (ih htail)
          · have heq : id = id1 := Classical.byContradiction (fun hneq => hne hneq)
            subst id
            simpa [create_undef_temps] using
              (PTree.gss (A := CompCert4Lean.Common.Values.val) id1
                (.Vundef) (create_undef_temps rest))

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Maps

theorem create_undef_temps_inv : create_undef_temps_invStatement := by
  intro vars id v h
  induction vars with
  | nil =>
      have hempty : PTree.get id (PTree.empty CompCert4Lean.Common.Values.val) = none :=
        PTree.gempty _ _
      change PTree.get id (PTree.empty CompCert4Lean.Common.Values.val) = some v at h
      rw [hempty] at h
      cases h
  | cons hd rest ih =>
      rcases hd with ⟨id1, ty1⟩
      change PTree.get id
        (PTree.set id1 (.Vundef) (create_undef_temps rest)) = some v at h
      have hspec := PTree.gsspec_proof (A := CompCert4Lean.Common.Values.val)
        id id1 (.Vundef) (create_undef_temps rest)
      rw [hspec] at h
      cases hp : CompCert4Lean.Lib.Coqlib.peq id id1 with
      | left heq =>
          subst id
          simp only [hp] at h
          constructor
          · exact (Option.some.inj h).symm
          · exact List.mem_cons_self
      | right hne =>
          have htail : PTree.get id (create_undef_temps rest) = some v := by
            simpa [hp] using h
          rcases ih htail with ⟨hv, hin⟩
          constructor
          · exact hv
          · exact List.mem_cons.mpr (Or.inr hin)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Maps

theorem create_undef_temps_exten : create_undef_temps_extenStatement := by
  intro id l1 l2 hmem
  have hdir : ∀ id l1 l2,
      (id ∈ var_names l1 → id ∈ var_names l2) →
      PTree.get id (create_undef_temps l1) = none ∨
        PTree.get id (create_undef_temps l1) =
          PTree.get id (create_undef_temps l2) := by
    intro id' l1' l2' hdir'
    cases hget : PTree.get id' (create_undef_temps l1') with
    | none => exact Or.inl rfl
    | some v =>
        right
        have hinv := create_undef_temps_inv l1' id' v hget
        rcases hinv with ⟨hv, hin⟩
        subst v
        have htarget : id' ∈ var_names l2' := hdir' hin
        obtain ⟨p, hp, hpl⟩ :=
          CompCert4Lean.Lib.Coqlib.list_in_map_inv
            (A := ident × type) (B := ident) Prod.fst l2' id'
            (by simpa [var_names] using htarget)
        rcases p with ⟨id1, ty1⟩
        have hid : id' = id1 := by simpa using hp
        subst id1
        exact (create_undef_temps_charact id' ty1 l2' hpl).symm
  rcases hdir id l1 l2 hmem.mp with hnone | heq
  · rcases hdir id l2 l1 hmem.mpr with hnone' | heq'
    · rw [hnone, hnone']
    · exact heq'.symm
  · exact heq

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem var_names_app : var_names_appStatement := by
  intro vars1 vars2
  simp only [CompCert4Lean.Cfrontend.Clight.var_names, List.map_append]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem filter_app : filter_appStatement := by
  intro A f l1 l2
  exact List.filter_append l1 l2

theorem filter_charact : filter_charactStatement := by
  intro A f x l
  exact List.mem_filter

theorem filter_norepet : filter_norepetStatement := by
  intro A f l h
  induction h with
  | nil =>
      exact CompCert4Lean.Lib.Coqlib.list_norepet.nil A
  | cons hd hnot htail ih =>
      cases hf : f hd with
      | false =>
          simpa [List.filter_cons, hf] using ih
      | true =>
          rw [List.filter_cons]
          simp [hf]
          apply CompCert4Lean.Lib.Coqlib.list_norepet.cons hd
          · intro hmem
            apply hnot
            exact (List.mem_filter.mp hmem).1
          · exact ih

theorem filter_map : filter_mapStatement := by
  intro A B f pa pb h l
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases ha : pa a with
      | false =>
          simp [List.filter, List.map, ha, h a, ih]
      | true =>
          simp [List.filter, List.map, ha, h a, ih]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Maps

theorem create_undef_temps_lifted : create_undef_temps_liftedStatement := by
  intro id f hparam
  apply create_undef_temps_exten
  unfold add_lifted
  rw [filter_app]
  unfold var_names at *
  repeat rw [List.map_append] at *
  constructor
  · intro hmem
    simp only [List.mem_append] at hmem ⊢
    rcases hmem with hvars | htemps
    · exact Or.inl (Or.inr hvars)
    · exact Or.inr htemps
  · intro hmem
    simp only [List.mem_append] at hmem ⊢
    rcases hmem with hparams | hrest
    · rcases hparams with hparam' | hvars
      · exfalso
        apply hparam
        obtain ⟨p, hp, hpl⟩ :=
          CompCert4Lean.Lib.Coqlib.list_in_map_inv _ _ Prod.fst _ _ hparam'
        have hp' : p ∈ f.fn_params := (List.mem_filter.mp hpl).1
        exact List.mem_map.mpr ⟨p, hp', hp.symm⟩
      · exact Or.inl hvars
    · exact Or.inr hrest

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib

theorem vars_and_temps_properties : vars_and_temps_propertiesStatement := by
  intro cenv params vars temps hnorepet hdisjoint
  have hsplit := (list_norepet_app _ _ _).mp hnorepet
  refine ⟨hsplit.1, ?_, ?_⟩
  · unfold remove_lifted
    unfold var_names
    have hfm := filter_map _ _ Prod.fst
      (fun idType => !(VSet.mem idType.1 cenv))
      (fun id => !(VSet.mem id cenv))
      (by intro a; rfl) (params ++ vars)
    refine hfm ▸ ?_
    apply filter_norepet
    have hnorepet' : list_norepet
        (List.map Prod.fst (params ++ vars)) := by
      rw [List.map_append]
      change list_norepet (List.map Prod.fst params ++ List.map Prod.fst vars) at hnorepet
      exact hnorepet
    exact hnorepet'
  · unfold add_lifted
    unfold var_names at *
    rw [List.map_append]
    intro x y hx hy hxy
    rcases (List.mem_append.mp hy) with hyvars | hytemps
    · obtain ⟨p, hp, hpl⟩ :=
        CompCert4Lean.Lib.Coqlib.list_in_map_inv _ _ Prod.fst _ _ hyvars
      have hpvars := (List.mem_filter.mp hpl).1
      have hyvars' : y ∈ List.map Prod.fst vars :=
        List.mem_map.mpr ⟨p, hpvars, hp.symm⟩
      exact hsplit.2.2 x y hx hyvars' hxy
    · exact hdisjoint x y hx hytemps hxy

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem match_envs_alloc_variables : match_envs_alloc_variablesStatement := by
  intro cfg p tp hprog
  dsimp only
  intro cenv m vars e m' temps j tm halloc hnorep hinj hbyval hdom
  have hempty : ∀ id, PTree.get id empty_env = none := by
    intro id
    simpa [empty_env] using (PTree.gempty (A := _) id)
  have hinit : env_initial_value empty_env m := by
    intro id b ty chunk hget
    rw [hempty id] at hget
    cases hget
  have hinit' := alloc_variables_initial_value p empty_env m vars e m' halloc hinit
  rcases match_alloc_variables cfg p tp hprog cenv empty_env m vars e m' halloc j tm empty_env hnorep hinj with
    ⟨j', te, tm', A, B, C, D, E, F, G, H⟩
  refine ⟨j', te, tm', A, ?_, B, C, D, E, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro id
      by_cases hid : id ∈ var_names vars
      · obtain ⟨p0, hp0, hplist⟩ :=
          CompCert4Lean.Lib.Coqlib.list_in_map_inv _ _ Prod.fst _ _
            (by simpa [var_names] using hid)
        rcases p0 with ⟨id0, ty0⟩
        have hid0 : id = id0 := by simpa using hp0
        subst id0
        rcases G id ty0 hplist with ⟨b, henv, hcase⟩
        cases hm : VSet.mem id cenv with
        | true =>
            simp only [hm, ↓reduceIte] at hcase
            have htenv : PTree.get id te = none := by
              rw [hcase.1]
              exact hempty _
            have hmode := hbyval id ty0 hplist hm
            rcases hmode with ⟨chunk, hmode⟩
            have hload := hinit' id b ty0 chunk henv hmode
            have hinadd : (id, ty0) ∈ add_lifted cenv vars temps := by
              unfold add_lifted
              apply List.mem_append.mpr
              left
              exact List.mem_filter.mpr ⟨hplist, hm⟩
            have htget := create_undef_temps_charact id ty0 _ hinadd
            exact match_var_lifted b ty0 chunk .Vundef .Vundef henv htenv hm
              hcase.2 hmode hload htget (Val.inject.val_inject_undef _)
        | false =>
            simp only [hm, ↓reduceIte] at hcase
            rcases hcase with ⟨tb, hte, hmap⟩
            exact match_var_not_lifted b ty0 tb henv hte hm hmap
      · have hmemfalse : VSet.mem id cenv = false := by
          cases hm : VSet.mem id cenv with
          | false => simpa using hm
          | true => exact False.elim (hid (hdom id hm))
        have hout := H id hid
        have henv : PTree.get id e = none := by
          rw [hout.1]
          exact hempty _
        have htenv : PTree.get id te = none := by
          rw [hout.2]
          exact hempty _
        exact match_var_not_local henv htenv hmemfalse
    · intro id v hget
      rcases create_undef_temps_inv temps id v hget with ⟨hv, hid⟩
      subst v
      change id ∈ List.map Prod.fst temps at hid
      obtain ⟨p0, hplist, hp0⟩ := List.mem_map.mp hid
      rcases p0 with ⟨id0, ty0⟩
      have hid0 : id0 = id := hp0
      subst id0
      have hinadd : (id, ty0) ∈ add_lifted cenv vars temps := by
        unfold add_lifted
        apply List.mem_append.mpr
        exact Or.inr hplist
      have htget := create_undef_temps_charact id ty0 _ hinadd
      refine ⟨⟨.Vundef, htget, Val.inject.val_inject_undef _⟩, ?_⟩
      intro _
      rfl
    · intro id1 b1 ty1 id2 b2 ty2 hget1 hget2 hneq
      apply alloc_variables_injective (globalenv p) id1 b1 ty1 id2 b2 ty2
        empty_env m vars e m' halloc
      · intro h1 h2 hne
        rw [hempty] at h1
        cases h1
      · intro id b ty hget
        rw [hempty _] at hget
        cases hget
      · exact hget1
      · exact hget2
      · exact hneq
    · intro id b ty hget
      rcases alloc_variables_range (globalenv p) id b ty empty_env m vars e m' halloc hget with h | h
      · rw [hempty] at h
        cases h
      · exact h
    · intro id b ty hget
      rcases alloc_variables_range (globalenv tp) id b ty empty_env tm
          (remove_lifted cenv vars) te tm' A hget with h | h
      · rw [hempty] at h
        cases h
      · exact h
    · intro id b' ty hte
      by_cases hid : id ∈ var_names vars
      · change id ∈ List.map Prod.fst vars at hid
        obtain ⟨p0, hplist, hp0⟩ := List.mem_map.mp hid
        rcases p0 with ⟨id0, ty0⟩
        have hid0 : id0 = id := hp0
        subst id0
        rcases G id ty0 hplist with ⟨b, henv, hcase⟩
        cases hm : VSet.mem id cenv with
        | true =>
            simp only [hm, ↓reduceIte] at hcase
            have hte0 : PTree.get id te = none := by
              rw [hcase.1]
              exact hempty _
            rw [hte0] at hte
            cases hte
        | false =>
            simp only [hm, ↓reduceIte] at hcase
            rcases hcase with ⟨tb, hte0, hmap⟩
            have heq : (tb, ty0) = (b', ty) := Option.some.inj (hte0.symm.trans hte)
            cases heq
            exact ⟨b, hmap, henv⟩
      · have hout := H id hid
        rw [hout.2] at hte
        rw [hempty _] at hte
        cases hte
    · intro id b' ty b delta hte hmap
      rcases alloc_variables_range (globalenv tp) id b' ty empty_env tm
          (remove_lifted cenv vars) te tm' A hte with h | h
      · rw [hempty] at h
        cases h
      · have hnotvalid : ¬ Mem.valid_block tm b' := by
          intro hv
          change Plt b' tm.nextblock at hv
          exact (Nat.not_lt_of_ge h.1) hv
        rcases F b b' delta hmap hnotvalid with ⟨id0, ty0, henv0, hte0, hdelta⟩
        have hid : id = id0 := by
          apply Classical.byContradiction
          intro hneq
          have hinj' := alloc_variables_injective (globalenv tp) id b' ty id0 b' ty0
            empty_env tm (remove_lifted cenv vars) te tm' A
            (by
              intro h1 h2 _
              rw [hempty] at h1
              cases h1)
            (by
              intro id1 b1 ty1 hget
              rw [hempty] at hget
              cases hget)
            hte hte0 hneq
          exact hinj' rfl
        subst id0
        have hty : (b', ty0) = (b', ty) := Option.some.inj (hte0.symm.trans hte)
        cases hty
        exact ⟨henv0, hdelta⟩
    · exact alloc_variables_nextblock (globalenv p) empty_env m vars e m' halloc
    · exact alloc_variables_nextblock (globalenv tp) empty_env tm
        (remove_lifted cenv vars) te tm' A
  · intro id ty hpair hfalse
    rcases G id ty hpair with ⟨b, henv, hcase⟩
    simp only [hfalse] at hcase
    rcases hcase with ⟨tb, hte, hmap⟩
    exact ⟨tb, hte⟩

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem blocks_of_env_translated : blocks_of_env_translatedStatement := by
  intro cfg p tp hprog e
  unfold CompCert4Lean.Cfrontend.Clight.blocks_of_env
  unfold CompCert4Lean.Cfrontend.Clight.block_of_binding
  rw [comp_env_preserved cfg p tp hprog]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.Ctypes

theorem blocks_of_env_no_overlap : blocks_of_env_no_overlapStatement := by
  intro ge j cenv e le m lo hi te tle tlo thi tm hme hinj hperms l
  induction l with
  | nil => simp [freelist_no_overlap]
  | cons a l ih =>
      cases a with
      | mk id bty =>
          cases bty with
          | mk b ty =>
              intro hnorep hte
              cases hnorep with
              | cons hd hnot htail =>
                  have hte0 : PTree.get id te = some (b, ty) := by
                    apply hte
                    simp
                  refine ⟨?_, ?_⟩
                  · apply ih htail
                    intro id' bty' hmem
                    apply hte id' bty'
                    simp [hmem]
                  · intro b' lo' hi' hmem
                    rcases List.mem_map.mp hmem with ⟨p, hpl, heq⟩
                    rcases p with ⟨id', b', ty'⟩
                    simp [CompCert4Lean.Cfrontend.Clight.block_of_binding] at heq
                    rcases heq with ⟨hb, hlo, hhi⟩
                    cases hb
                    have hte' : PTree.get id' te = some (b', ty') := by
                      apply hte id' (b', ty')
                      simp [hpl]
                    have hid' : id' ≠ id := by
                      intro heqid
                      subst id'
                      apply hnot
                      exact List.mem_map.mpr ⟨(id, b', ty'), hpl, rfl⟩
                    have hid : id ≠ id' := fun h => hid' h.symm
                    by_cases hsz : ZArith.BinInt.Z.le (sizeof ge.genv_cenv ty) .Z0
                    · exact Or.inr (Or.inr (by rw [← hlo]; exact hsz))
                    by_cases hsz' : ZArith.BinInt.Z.le (sizeof ge.genv_cenv ty') .Z0
                    · exact Or.inr (Or.inl (by rw [← hhi]; exact hsz'))
                    have hne : b ≠ b' := by
                      rcases hme.me_mapped id b ty hte0 with ⟨b0, hmap, hsrc0⟩
                      rcases hme.me_mapped id' b' ty' hte' with ⟨b0', hmap', hsrc'⟩
                      have hb0 : b0 ≠ b0' := by
                        apply hme.me_inj id b0 ty id' b0' ty' hsrc0 hsrc' hid
                      intro hbb
                      subst b'
                      have hmaps := hinj.mi_no_overlap b0 b .Z0 b0' b .Z0 .Z0 .Z0
                        hb0 hmap hmap'
                      have hperm0 : Mem.perm m b0 .Z0 .Max .Nonempty := by
                        apply Mem.perm_implies m b0 .Z0 .Max .Freeable .Nonempty
                          (Mem.perm_cur_max m b0 .Z0 .Freeable
                            (hperms id b0 ty hsrc0 .Z0 ⟨by
                              change intOfZ .Z0 ≤ intOfZ .Z0
                              omega, by
                              change intOfZ .Z0 < intOfZ (sizeof ge.genv_cenv ty)
                              change ¬ intOfZ (sizeof ge.genv_cenv ty) ≤ intOfZ .Z0 at hsz
                              omega⟩))
                        exact .perm_F_any _
                      have hperm0' : Mem.perm m b0' .Z0 .Max .Nonempty := by
                        apply Mem.perm_implies m b0' .Z0 .Max .Freeable .Nonempty
                          (Mem.perm_cur_max m b0' .Z0 .Freeable
                            (hperms id' b0' ty' hsrc' .Z0 ⟨by
                              change intOfZ .Z0 ≤ intOfZ .Z0
                              omega, by
                              change intOfZ .Z0 < intOfZ (sizeof ge.genv_cenv ty')
                              change ¬ intOfZ (sizeof ge.genv_cenv ty') ≤ intOfZ .Z0 at hsz'
                              omega⟩))
                        exact .perm_F_any _
                      have := hmaps hperm0 hperm0'
                      simp at this
                    exact Or.inl hne.symm

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Clight

theorem assign_loc_nextblock : assign_loc_nextblockStatement := by
  intro ge ty m b ofs bf v m' hassign
  cases hassign with
  | assign_loc_value v chunk m' hmode hstore =>
      exact Mem.nextblock_store _ _ _ _ _ _ hstore
  | assign_loc_copy b' ofs' bytes m' hmode halignSource halignTarget hseparated hload hstore =>
      exact Mem.nextblock_storebytes _ _ _ _ _ hstore
  | assign_loc_bitfield sz sg pos width v m' v' hstore =>
      cases hstore with
      | store_bitfield_intro sz sg1 attr sg pos width m addr c n m' hpos hwidth
          hcarrier hsg hload hstore =>
          exact Mem.nextblock_store _ _ _ _ _ _ hstore

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Clight

theorem bind_parameters_nextblock : bind_parameters_nextblockStatement := by
  intro ge e m params args m' hbind
  induction hbind with
  | nil => rfl
  | cons m id ty params v1 vl b m1 m2 hfind hassign hrest ih =>
      rw [ih]
      exact assign_loc_nextblock ge.genv_cenv ty m b
        CompCert4Lean.Lib.Integers.Ptrofs.zero .Full v1 m1 hassign

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Clight

theorem bind_parameters_load : bind_parameters_loadStatement := by
  intro ge e chunk b ofs hne m params args m' hbind
  induction hbind with
  | nil => rfl
  | cons m id ty params v1 vl b0 m1 m2 hfind hassign hrest ih =>
      rw [ih]
      have hneq : b ≠ b0 := hne id b0 ty hfind
      cases hassign with
      | assign_loc_value _ chunk0 m1 _ hstore =>
          simp [Mem.storev] at hstore
          exact Mem.load_store_other chunk0 m b0
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned
              CompCert4Lean.Lib.Integers.Ptrofs.zero) _ m1 hstore
            chunk b ofs (Or.inl hneq)
      | assign_loc_copy b' ofs' bytes m1 hmode halignSource halignTarget hseparated hload hstore =>
          exact Mem.load_storebytes_other m b0
            (CompCert4Lean.Lib.Integers.Ptrofs.unsigned
              CompCert4Lean.Lib.Integers.Ptrofs.zero) bytes m1 hstore
            chunk b ofs (Or.inl hneq)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes

private theorem slp_pmap_get_set_same {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i i with
  | left h => simp [hpeq]
  | right h => exact False.elim (h rfl)

private theorem slp_pmap_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y | none => m.1) =
    (match PTree.get i m.2 with | some y => y | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem slp_perm_of_free (m m1 : Mem.mem) (b' : positive) (lo hi : Z)
    (hfree : Mem.free m b' lo hi = some m1) :
    ∀ b ofs (k : perm_kind) (p : permission),
      Mem.perm m1 b ofs k p → Mem.perm m b ofs k p := by
  intro b ofs k p hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm1
    subst m1
    unfold Mem.perm at hp ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [slp_pmap_get_set_same] at hp
      split at hp
      · exact False.elim hp
      · exact hp
    · dsimp [Mem.unchecked_free] at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [slp_pmap_get_set_other _ _ _ _ hb] at hp
      exact hp
  next hcond => cases hfree

private theorem slp_perm_freelist :
    ∀ (l : List (positive × Z × Z)) (m m' : Mem.mem)
      (b : positive) (ofs : Z) (k : perm_kind) (p : permission),
      Mem.free_list m l = some m' → Mem.perm m' b ofs k p → Mem.perm m b ofs k p := by
  intro l
  induction l with
  | nil =>
      intro m m' b ofs k p hfree hp
      simp [Mem.free_list] at hfree
      cases hfree
      exact hp
  | cons x rest ih =>
      intro m m' b ofs k p hfree hp
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          have hp1 : Mem.perm m1 b ofs k p :=
            ih m1 m' b ofs k p hrest hp
          exact slp_perm_of_free m m1 x.1 x.2.1 x.2.2 hfm b ofs k p hp1

private theorem slp_perm_free_2 (m m' : Mem.mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ ofs (k : perm_kind) (p : permission),
      ZArith.BinInt.Z.le lo ofs → ZArith.BinInt.Z.lt ofs hi → ¬ Mem.perm m' b ofs k p := by
  intro ofs k p hlo hhi hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm'] at hp
    unfold Mem.perm at hp
    dsimp [Mem.unchecked_free] at hp
    change Mem.perm_order'
      ((PMap.get b (PMap.set b
        (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
    rw [slp_pmap_get_set_same] at hp
    split at hp
    · exact hp
    · rename_i hnot
      exfalso
      apply hnot
      change (ZArith.BinInt.Z.leb lo ofs && ZArith.BinInt.Z.ltb ofs hi) = true
      have hlo' : intOfZ lo ≤ intOfZ ofs := by
        change intOfZ lo ≤ intOfZ ofs
        exact hlo
      have hhi' : intOfZ ofs < intOfZ hi := by
        change intOfZ ofs < intOfZ hi
        exact hhi
      simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb, hlo', hhi']
  next hcond => cases hfree

private theorem slp_free_list_no_perm (l : List (positive × Z × Z))
    (m m' : Mem.mem) (hfree : Mem.free_list m l = some m') :
    ∀ b lo hi, (b, lo, hi) ∈ l →
      ∀ ofs (k : perm_kind) (p : permission),
        ZArith.BinInt.Z.le lo ofs → ZArith.BinInt.Z.lt ofs hi → ¬ Mem.perm m' b ofs k p := by
  induction l generalizing m m' with
  | nil =>
      intro b lo hi hin
      cases hin
  | cons x rest ih =>
      intro b lo hi hin ofs k p hlo hhi hp
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          cases (_root_.List.mem_cons.mp hin) with
          | inl heq =>
              cases heq
              have hp1 : Mem.perm m1 b ofs k p :=
                slp_perm_freelist rest m1 m' b ofs k p hrest hp
              exact slp_perm_free_2 m m1 b lo hi hfm ofs k p hlo hhi hp1
          | inr htail =>
              exact ih m1 m' hrest b lo hi htail ofs k p hlo hhi hp

theorem free_blocks_of_env_perm_1 : free_blocks_of_env_perm_1Statement := by
  intro ce m e m' id b ty ofs k permission hfree hget hperm hbounds
  have hmem : (b, (.Z0 : Z), sizeof ce.genv_cenv ty) ∈ blocks_of_env ce e := by
    unfold blocks_of_env
    apply List.mem_map.mpr
    refine ⟨(id, (b, ty)), ?_, ?_⟩
    · exact PTree.elements_correct_proof e id (v := (b, ty)) hget
    · rfl
  exact slp_free_list_no_perm (blocks_of_env ce e) m m' hfree
    b (.Z0 : Z) (sizeof ce.genv_cenv ty) hmem ofs k permission
    hbounds.1 hbounds.2 hperm

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem slp_free_range_perm (m : Mem.mem) (b : positive) (lo hi : Z)
    (m' : Mem.mem) (hfree : Mem.free m b lo hi = some m') :
    Mem.range_perm m b lo hi .Cur .Freeable := by
  unfold Mem.free at hfree
  cases hr : Mem.range_perm_dec m b lo hi .Cur .Freeable with
  | left hp =>
      simp [hr] at hfree
      cases hfree
      exact hp
  | right hn =>
      simp [hr] at hfree
      cases hfree.1

private theorem slp_free_list_freeable :
    ∀ l m m', Mem.free_list m l = some m' →
      ∀ b lo hi, (b, lo, hi) ∈ l → Mem.range_perm m b lo hi .Cur .Freeable := by
  intro l
  induction l with
  | nil =>
      intro m m' hfree b lo hi hin
      cases hin
  | cons a rest ih =>
      intro m m' hfree b lo hi hin
      rcases a with ⟨b0, lo0, hi0⟩
      change (match Mem.free m b0 lo0 hi0 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m b0 lo0 hi0 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          cases (_root_.List.mem_cons.mp hin) with
          | inl heq =>
              injection heq with hb hlo
              subst b
              cases hlo
              exact slp_free_range_perm m b0 lo hi m1 hfm
          | inr htail =>
              have hrest : Mem.free_list m1 rest = some m' := hfree
              have hrange := ih m1 m' hrest b lo hi htail
              intro ofs hof
              exact slp_perm_of_free m m1 b0 lo0 hi0 hfm b ofs .Cur .Freeable
                (hrange ofs hof)

theorem free_list_perm' : free_list_perm'Statement := by
  intro b lo hi l m m' hfree hin
  exact slp_free_list_freeable l m m' hfree b lo hi hin

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

theorem free_blocks_of_env_perm_2 : free_blocks_of_env_perm_2Statement := by
  intro ce m e m' id b ty hfree hget
  apply free_list_perm' b (.Z0 : Z)
    (CompCert4Lean.Cfrontend.Ctypes.sizeof ce.genv_cenv ty)
    (CompCert4Lean.Cfrontend.Clight.blocks_of_env ce e) m m' hfree
  unfold CompCert4Lean.Cfrontend.Clight.blocks_of_env
  apply List.mem_map.mpr
  refine ⟨(id, (b, ty)), ?_, ?_⟩
  · exact PTree.elements_correct_proof e id (v := (b, ty)) hget
  · rfl

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps

private theorem slp_range_perm_free (m : Mem.mem) (b : positive) (lo hi : Z)
    (hperm : Mem.range_perm m b lo hi .Cur .Freeable) :
    ∃ m', Mem.free m b lo hi = some m' := by
  cases hr : Mem.range_perm_dec m b lo hi .Cur .Freeable with
  | left hp =>
      refine ⟨Mem.unchecked_free m b lo hi, ?_⟩
      unfold Mem.free
      rw [hr]
      rfl
  | right hn =>
      exact False.elim (hn hperm)

private theorem slp_perm_free_1 (m m' : Mem.mem) (b' : positive) (lo hi : Z)
    (hfree : Mem.free m b' lo hi = some m') :
    ∀ b ofs (k : perm_kind) (p : permission),
      (b ≠ b' ∨ ZArith.BinInt.Z.lt ofs lo ∨
        ZArith.BinInt.Z.le hi ofs) →
      Mem.perm m b ofs k p → Mem.perm m' b ofs k p := by
  intro b ofs k p hout hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm']
    unfold Mem.perm at hp ⊢
    dsimp [Mem.unchecked_free] at ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order' ((PMap.get b' m.mem_access) ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [slp_pmap_get_set_same]
      split
      · rename_i hin
        exfalso
        rcases hout with hne | hlt | hge
        · exact hne rfl
        · change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hlo' : intOfZ lo ≤ intOfZ ofs := by
            simpa [ZArith.BinInt.Z.leb] using hin'.1
          change intOfZ ofs < intOfZ lo at hlt
          omega
        · change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hhi' : intOfZ ofs < intOfZ hi := by
            simpa [ZArith.BinInt.Z.ltb] using hin'.2
          change intOfZ hi ≤ intOfZ ofs at hge
          omega
      · exact hp
    · change Mem.perm_order' (PMap.get b m.mem_access ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [slp_pmap_get_set_other _ _ _ _ hb]
      exact hp
  next hcond => cases hfree

theorem can_free_list : can_free_listStatement := by
  intro l
  induction l with
  | nil =>
      intro m hperms hno
      exact ⟨m, by rfl⟩
  | cons a rest ih =>
      intro m hperms hno
      rcases a with ⟨b, lo, hi⟩
      change freelist_no_overlap rest ∧
        (∀ b' lo' hi', (b', lo', hi') ∈ rest →
          b' ≠ b ∨ ZArith.BinInt.Z.le hi' lo ∨
            ZArith.BinInt.Z.le hi lo') at hno
      rcases slp_range_perm_free m b lo hi
        (hperms b lo hi (_root_.List.mem_cons_self)) with ⟨m1, hfree⟩
      have hperms1 : ∀ b' lo' hi', (b', lo', hi') ∈ rest →
          Mem.range_perm m1 b' lo' hi' .Cur .Freeable := by
        intro b' lo' hi' hmem
        intro ofs hof
        apply slp_perm_free_1 m m1 b lo hi hfree b' ofs .Cur .Freeable
        · rcases hno.2 b' lo' hi' hmem with hne | hbefore | hafter
          · exact Or.inl hne
          · right
            left
            change intOfZ ofs < intOfZ lo
            change intOfZ hi' ≤ intOfZ lo at hbefore
            change intOfZ lo' ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi' at hof
            omega
          · right
            right
            change intOfZ hi ≤ intOfZ ofs
            change intOfZ hi ≤ intOfZ lo' at hafter
            change intOfZ lo' ≤ intOfZ ofs ∧ intOfZ ofs < intOfZ hi' at hof
            omega
        · exact hperms b' lo' hi'
            (_root_.List.mem_cons.mpr (Or.inr hmem)) ofs hof
      rcases ih m1 hperms1 hno.1 with ⟨m2, htail⟩
      refine ⟨m2, ?_⟩
      change (match Mem.free m b lo hi with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m2
      rw [hfree]
      exact htail

end CompCert4Lean.Cfrontend.SimplLocalsproof
namespace CompCert4Lean.Cfrontend.SimplLocalsproof
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Lib.Coqlib

private theorem slp2_pmap_get_set_same {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i i with
  | left h => simp [hpeq]
  | right h => exact False.elim (h rfl)

private theorem slp2_pmap_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y | none => m.1) =
    (match PTree.get i m.2 with | some y => y | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem slp2_perm_of_free (m m1 : Mem.mem) (b' : positive) (lo hi : Z)
    (hfree : Mem.free m b' lo hi = some m1) :
    ∀ b ofs (k : perm_kind) (p : permission),
      Mem.perm m1 b ofs k p → Mem.perm m b ofs k p := by
  intro b ofs k p hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm1
    subst m1
    unfold Mem.perm at hp ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [slp2_pmap_get_set_same] at hp
      split at hp
      · exact False.elim hp
      · exact hp
    · dsimp [Mem.unchecked_free] at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [slp2_pmap_get_set_other _ _ _ _ hb] at hp
      exact hp
  next hcond => cases hfree

private theorem slp2_perm_free_1 (m m' : Mem.mem) (b' : positive) (lo hi : Z)
    (hfree : Mem.free m b' lo hi = some m') :
    ∀ b ofs (k : perm_kind) (p : permission),
      (b ≠ b' ∨ ZArith.BinInt.Z.lt ofs lo ∨
        ZArith.BinInt.Z.le hi ofs) →
      Mem.perm m b ofs k p → Mem.perm m' b ofs k p := by
  intro b ofs k p hout hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm']
    unfold Mem.perm at hp ⊢
    dsimp [Mem.unchecked_free] at ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order' ((PMap.get b' m.mem_access) ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [slp2_pmap_get_set_same]
      split
      · rename_i hin
        exfalso
        rcases hout with hne | hlt | hge
        · exact hne rfl
        · change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hlo' : intOfZ lo ≤ intOfZ ofs := by
            simpa [ZArith.BinInt.Z.leb] using hin'.1
          change intOfZ ofs < intOfZ lo at hlt
          omega
        · change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hhi' : intOfZ ofs < intOfZ hi := by
            simpa [ZArith.BinInt.Z.ltb] using hin'.2
          change intOfZ hi ≤ intOfZ ofs at hge
          omega
      · exact hp
    · change Mem.perm_order' (PMap.get b m.mem_access ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [slp2_pmap_get_set_other _ _ _ _ hb]
      exact hp
  next hcond => cases hfree

private theorem slp2_nextblock_free (m : Mem.mem) (b : positive) (lo hi : Z)
    (m' : Mem.mem) (hfree : Mem.free m b lo hi = some m') :
    m'.nextblock = m.nextblock := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond => cases hfree

private theorem slp2_free_contents (m m' : Mem.mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    m'.mem_contents = m.mem_contents := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond => cases hfree

private theorem slp2_outside_interval (x lo hi : Z) :
    ¬ (ZArith.BinInt.Z.le lo x ∧ ZArith.BinInt.Z.lt x hi) →
      ZArith.BinInt.Z.lt x lo ∨ ZArith.BinInt.Z.le hi x := by
  intro h
  by_cases hlt : ZArith.BinInt.Z.lt x lo
  · exact Or.inl hlt
  by_cases hge : ZArith.BinInt.Z.le hi x
  · exact Or.inr hge
  exfalso
  apply h
  constructor
  · change intOfZ lo ≤ intOfZ x
    change ¬ intOfZ x < intOfZ lo at hlt
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega
  · change intOfZ x < intOfZ hi
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega

private theorem slp2_free_right_inject
    (f : CompCert4Lean.Common.Values.Val.meminj) (m tm tm' : Mem.mem)
    (b : positive) (lo hi : Z)
    (hinj : Mem.inject f m tm)
    (hfree : Mem.free tm b lo hi = some tm')
    (hside : ∀ b1 delta ofs (k : perm_kind) (p : permission),
      f b1 = some (b, delta) →
      Mem.perm m b1 ofs k p →
      ZArith.BinInt.Z.le lo (ZArith.BinInt.Z.add ofs delta) ∧
        ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) hi → False) :
    Mem.inject f m tm' := by
  have hnext := slp2_nextblock_free tm b lo hi tm' hfree
  have hcont := slp2_free_contents tm tm' b lo hi hfree
  refine {
    mi_inj := ?_,
    mi_freeblocks := hinj.mi_freeblocks,
    mi_mappedblocks := ?_,
    mi_no_overlap := hinj.mi_no_overlap,
    mi_representable := hinj.mi_representable,
    mi_perm_inv := ?_ }
  · refine { mi_perm := ?_, mi_align := hinj.mi_inj.mi_align, mi_memval := ?_ }
    · intro b1 b2 delta ofs k p hmap hp
      apply slp2_perm_free_1 tm tm' b lo hi hfree b2
        (ZArith.BinInt.Z.add ofs delta) k p
      · by_cases hb : b2 = b
        · subst b2
          by_cases hinside :
              ZArith.BinInt.Z.le lo (ZArith.BinInt.Z.add ofs delta) ∧
                ZArith.BinInt.Z.lt (ZArith.BinInt.Z.add ofs delta) hi
          · exact False.elim (hside b1 delta ofs k p hmap hp hinside)
          · rcases slp2_outside_interval (ZArith.BinInt.Z.add ofs delta) lo hi
              hinside with hlt | hge
            · exact Or.inr (Or.inl hlt)
            · exact Or.inr (Or.inr hge)
        · exact Or.inl hb
      · exact hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap hp
    · intro b1 ofs b2 delta hmap hp
      have hmv := hinj.mi_inj.mi_memval b1 ofs b2 delta hmap hp
      simpa [hcont] using hmv
  · intro b1 b2 delta hmap
    have hv := hinj.mi_mappedblocks b1 b2 delta hmap
    change CompCert4Lean.Lib.Coqlib.Plt b2 tm'.nextblock
    rw [hnext]
    exact hv
  · intro b1 ofs b2 delta k p hmap hp2
    exact hinj.mi_perm_inv b1 ofs b2 delta k p hmap
      (slp2_perm_of_free tm tm' b lo hi hfree b2
        (ZArith.BinInt.Z.add ofs delta) k p hp2)

theorem free_list_right_inject : free_list_right_injectStatement := by
  intro j m1 l m2 m2' hinj hfree hside
  induction l generalizing m2 m2' with
  | nil =>
      simp [Mem.free_list] at hfree
      cases hfree
      exact hinj
  | cons x rest ih =>
      rcases x with ⟨b, lo, hi⟩
      change (match Mem.free m2 b lo hi with
        | none => none
        | some m21 => Mem.free_list m21 rest) = some m2' at hfree
      cases hfm : Mem.free m2 b lo hi with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m21 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m21 rest = some m2' := hfree
          have hinj1 : Mem.inject j m1 m21 := by
            apply slp2_free_right_inject j m1 m2 m21 b lo hi hinj hfm
            intro b1 delta ofs k p hmap hp hinside
            exact hside (b1 := b1) (b2 := b) (delta := delta) (lo := lo)
              (hi := hi) (ofs := ofs) (k := k) (permission := p) hmap
              (_root_.List.mem_cons.mpr (Or.inl rfl)) hp hinside
          apply ih m21 m2' hinj1 hrest
          intro b1 b2 delta lo' hi' ofs k p hmap hin hp hinside
          exact hside (b1 := b1) (b2 := b2) (delta := delta) (lo := lo')
            (hi := hi') (ofs := ofs) (k := k) (permission := p) hmap
           (_root_.List.mem_cons.mpr (Or.inr hin)) hp hinside

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Lib.Maps
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.Ctypes

private theorem slp3_pmap_get_set_same {A : Type} (i : positive) (x : A)
    (m : PMap.t A) : PMap.get i (PMap.set i x m) = x := by
  change (match PTree.get i (PTree.set i x m.2) with
    | some y => y | none => m.1) = x
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i i with
  | left h => simp [hpeq]
  | right h => exact False.elim (h rfl)

private theorem slp3_pmap_get_set_other {A : Type} (i j : positive) (x : A)
    (m : PMap.t A) (h : i ≠ j) : PMap.get i (PMap.set j x m) = PMap.get i m := by
  change (match PTree.get i (PTree.set j x m.2) with
    | some y => y | none => m.1) =
    (match PTree.get i m.2 with | some y => y | none => m.1)
  rw [PTree.gsspec_proof]
  cases hpeq : CompCert4Lean.Lib.Coqlib.peq i j with
  | left hij => exact False.elim (h hij)
  | right hne => simp [hpeq]

private theorem slp3_perm_of_free (m m1 : Mem.mem) (b' : positive) (lo hi : Z)
    (hfree : Mem.free m b' lo hi = some m1) :
    ∀ b ofs (k : perm_kind) (p : permission),
      Mem.perm m1 b ofs k p → Mem.perm m b ofs k p := by
  intro b ofs k p hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm1
    subst m1
    unfold Mem.perm at hp ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [slp3_pmap_get_set_same] at hp
      split at hp
      · exact False.elim hp
      · exact hp
    · dsimp [Mem.unchecked_free] at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
      rw [slp3_pmap_get_set_other _ _ _ _ hb] at hp
      exact hp
  next hcond => cases hfree

private theorem slp3_perm_free_1 (m m' : Mem.mem) (b' : positive) (lo hi : Z)
    (hfree : Mem.free m b' lo hi = some m') :
    ∀ b ofs (k : perm_kind) (p : permission),
      (b ≠ b' ∨ ZArith.BinInt.Z.lt ofs lo ∨
        ZArith.BinInt.Z.le hi ofs) →
      Mem.perm m b ofs k p → Mem.perm m' b ofs k p := by
  intro b ofs k p hout hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm']
    unfold Mem.perm at hp ⊢
    dsimp [Mem.unchecked_free] at ⊢
    by_cases hb : b = b'
    · subst b
      change Mem.perm_order' ((PMap.get b' m.mem_access) ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b' (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
        at ⊢
      rw [slp3_pmap_get_set_same]
      split
      · rename_i hin
        exfalso
        rcases hout with hne | hlt | hge
        · exact hne rfl
        · change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hlo' : intOfZ lo ≤ intOfZ ofs := by
            simpa [ZArith.BinInt.Z.leb] using hin'.1
          change intOfZ ofs < intOfZ lo at hlt
          omega
        · change (ZArith.BinInt.Z.leb lo ofs &&
            ZArith.BinInt.Z.ltb ofs hi) = true at hin
          have hin' := Bool.and_eq_true_iff.mp hin
          have hhi' : intOfZ ofs < intOfZ hi := by
            simpa [ZArith.BinInt.Z.ltb] using hin'.2
          change intOfZ hi ≤ intOfZ ofs at hge
          omega
      · exact hp
    · change Mem.perm_order' (PMap.get b m.mem_access ofs k) p at hp
      change Mem.perm_order'
        ((PMap.get b (PMap.set b'
          (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p
      rw [slp3_pmap_get_set_other _ _ _ _ hb]
      exact hp
  next hcond => cases hfree

private theorem slp3_perm_free_2 (m m' : Mem.mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ ofs (k : perm_kind) (p : permission),
      ZArith.BinInt.Z.le lo ofs → ZArith.BinInt.Z.lt ofs hi →
      ¬ Mem.perm m' b ofs k p := by
  intro ofs k p hlo hhi hp
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    rw [← hm'] at hp
    unfold Mem.perm at hp
    dsimp [Mem.unchecked_free] at hp
    change Mem.perm_order'
      ((PMap.get b (PMap.set b
        (fun (ofs : Z) (k : perm_kind) => _) m.mem_access)) ofs k) p at hp
    rw [slp3_pmap_get_set_same] at hp
    split at hp
    · exact hp
    · rename_i hnot
      exfalso
      apply hnot
      change (ZArith.BinInt.Z.leb lo ofs &&
        ZArith.BinInt.Z.ltb ofs hi) = true
      have hlo' : intOfZ lo ≤ intOfZ ofs := by exact hlo
      have hhi' : intOfZ ofs < intOfZ hi := by exact hhi
      simp [ZArith.BinInt.Z.leb, ZArith.BinInt.Z.ltb, hlo', hhi']
  next hcond => cases hfree

private theorem slp3_perm_freelist :
    ∀ (l : List (positive × Z × Z)) (m m' : Mem.mem)
      (b : positive) (ofs : Z) (k : perm_kind) (p : permission),
      Mem.free_list m l = some m' → Mem.perm m' b ofs k p → Mem.perm m b ofs k p := by
  intro l
  induction l with
  | nil =>
      intro m m' b ofs k p hfree hp
      simp [Mem.free_list] at hfree
      cases hfree
      exact hp
  | cons x rest ih =>
      intro m m' b ofs k p hfree hp
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          have hp1 : Mem.perm m1 b ofs k p := ih m1 m' b ofs k p hrest hp
          exact slp3_perm_of_free m m1 x.1 x.2.1 x.2.2 hfm b ofs k p hp1

private theorem slp3_free_list_no_perm (l : List (positive × Z × Z))
    (m m' : Mem.mem) (hfree : Mem.free_list m l = some m') :
    ∀ b lo hi, (b, lo, hi) ∈ l →
      ∀ ofs (k : perm_kind) (p : permission),
        ZArith.BinInt.Z.le lo ofs → ZArith.BinInt.Z.lt ofs hi →
        ¬ Mem.perm m' b ofs k p := by
  induction l generalizing m m' with
  | nil =>
      intro b lo hi hin
      cases hin
  | cons x rest ih =>
      intro b lo hi hin ofs k p hlo hhi hp
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          cases (_root_.List.mem_cons.mp hin) with
          | inl heq =>
              cases heq
              have hp1 : Mem.perm m1 b ofs k p :=
                slp3_perm_freelist rest m1 m' b ofs k p hrest hp
              exact slp3_perm_free_2 m m1 b lo hi hfm ofs k p hlo hhi hp1
          | inr htail =>
              exact ih m1 m' hrest b lo hi htail ofs k p hlo hhi hp

private theorem slp3_nextblock_free (m : Mem.mem) (b : positive) (lo hi : Z)
    (m' : Mem.mem) (hfree : Mem.free m b lo hi = some m') :
    m'.nextblock = m.nextblock := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond => cases hfree

private theorem slp3_free_contents (m m' : Mem.mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    m'.mem_contents = m.mem_contents := by
  unfold Mem.free at hfree
  split at hfree
  next hcond =>
    injection hfree with hm'
    subst m'
    rfl
  next hcond => cases hfree

private theorem slp3_outside_interval (x lo hi : Z) :
    ¬ (ZArith.BinInt.Z.le lo x ∧ ZArith.BinInt.Z.lt x hi) →
      ZArith.BinInt.Z.lt x lo ∨ ZArith.BinInt.Z.le hi x := by
  intro h
  by_cases hlt : ZArith.BinInt.Z.lt x lo
  · exact Or.inl hlt
  by_cases hge : ZArith.BinInt.Z.le hi x
  · exact Or.inr hge
  exfalso
  apply h
  constructor
  · change intOfZ lo ≤ intOfZ x
    change ¬ intOfZ x < intOfZ lo at hlt
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega
  · change intOfZ x < intOfZ hi
    change ¬ intOfZ hi ≤ intOfZ x at hge
    omega

private theorem slp3_perm_free_of_max
    (m m' : Mem.mem) (b : positive) (lo hi : Z)
    (hfree : Mem.free m b lo hi = some m') :
    ∀ b1 ofs (k : perm_kind) (p : permission),
      Mem.perm m' b1 ofs .Max .Nonempty →
      Mem.perm m b1 ofs k p → Mem.perm m' b1 ofs k p := by
  intro b1 ofs k p hmax hp
  have hfl : Mem.free_list m [(b, lo, hi)] = some m' := by
    change (match Mem.free m b lo hi with
      | none => none
      | some m1 => some m1) = some m'
    rw [hfree]
  by_cases hb : b1 = b
  · subst b1
    have hout : ¬ (ZArith.BinInt.Z.le lo ofs ∧
        ZArith.BinInt.Z.lt ofs hi) := by
      intro hins
      have hno := slp3_free_list_no_perm [(b, lo, hi)] m m' hfl
        b lo hi (_root_.List.mem_cons.mpr (Or.inl rfl))
        ofs .Max .Nonempty hins.1 hins.2
      exact hno hmax
    rcases slp3_outside_interval ofs lo hi hout with hlt | hge
    · exact slp3_perm_free_1 m m' b lo hi hfree b ofs k p
        (Or.inr (Or.inl hlt)) hp
    · exact slp3_perm_free_1 m m' b lo hi hfree b ofs k p
        (Or.inr (Or.inr hge)) hp
  · exact slp3_perm_free_1 m m' b lo hi hfree b1 ofs k p
      (Or.inl hb) hp

private theorem slp3_free_left_inject
    (f : CompCert4Lean.Common.Values.Val.meminj) (m tm tm' : Mem.mem)
    (b : positive) (lo hi : Z)
    (hinj : Mem.inject f m tm)
    (hfree : Mem.free m b lo hi = some tm') :
    Mem.inject f tm' tm := by
  have hnext := slp3_nextblock_free m b lo hi tm' hfree
  have hcont := slp3_free_contents m tm' b lo hi hfree
  refine {
    mi_inj := ?_,
    mi_freeblocks := ?_,
    mi_mappedblocks := hinj.mi_mappedblocks,
    mi_no_overlap := ?_,
    mi_representable := ?_,
    mi_perm_inv := ?_ }
  · refine { mi_perm := ?_, mi_align := ?_, mi_memval := ?_ }
    · intro b1 b2 delta ofs k p hmap hp
      exact hinj.mi_inj.mi_perm b1 b2 delta ofs k p hmap
        (slp2_perm_of_free m tm' b lo hi hfree b1 ofs k p hp)
    · intro b1 b2 delta chunk ofs p hmap hrange
      apply hinj.mi_inj.mi_align b1 b2 delta chunk ofs p hmap
      intro q hq
      exact slp2_perm_of_free m tm' b lo hi hfree b1 q .Max p
        (hrange q hq)
    · intro b1 ofs b2 delta hmap hp
      have hmv := hinj.mi_inj.mi_memval b1 ofs b2 delta hmap
        (slp2_perm_of_free m tm' b lo hi hfree b1 ofs .Cur .Readable hp)
      simpa [hcont] using hmv
  · intro b1 hvalid
    exact hinj.mi_freeblocks b1 (by
      intro hvalid_old
      apply hvalid
      change CompCert4Lean.Lib.Coqlib.Plt b1 tm'.nextblock
      rw [hnext]
      exact hvalid_old)
  · intro b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hneq hmap1 hmap2 hp1 hp2
    exact hinj.mi_no_overlap b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 hneq hmap1 hmap2
      (slp2_perm_of_free m tm' b lo hi hfree b1 ofs1 .Max .Nonempty hp1)
      (slp2_perm_of_free m tm' b lo hi hfree b2 ofs2 .Max .Nonempty hp2)
  · intro b1 b2 delta ofs hmap hperm
    apply hinj.mi_representable b1 b2 delta ofs hmap
    rcases hperm with hperm | hperm
    · exact Or.inl (slp2_perm_of_free m tm' b lo hi hfree b1
        (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) .Max .Nonempty hperm)
    · exact Or.inr (slp2_perm_of_free m tm' b lo hi hfree b1
        (ZArith.BinInt.Z.sub
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) (.Zpos .xH))
        .Max .Nonempty hperm)
  · intro b1 ofs b2 delta k p hmap hp
    by_cases hmax : Mem.perm tm' b1 ofs .Max .Nonempty
    · rcases hinj.mi_perm_inv b1 ofs b2 delta k p hmap hp with hpold | hnone
      · exact Or.inl (slp3_perm_free_of_max m tm' b lo hi hfree
          b1 ofs k p hmax hpold)
      · exact False.elim (hnone
          (slp2_perm_of_free m tm' b lo hi hfree b1 ofs .Max .Nonempty hmax))
    · exact Or.inr hmax

private theorem slp3_free_list_left_inject
    (f : CompCert4Lean.Common.Values.Val.meminj) :
    ∀ l m m' tm, Mem.inject f m tm →
      Mem.free_list m l = some m' → Mem.inject f m' tm := by
  intro l
  induction l with
  | nil =>
      intro m m' tm hinj hfree
      simp [Mem.free_list] at hfree
      cases hfree
      exact hinj
  | cons x rest ih =>
      intro m m' tm hinj hfree
      rcases x with ⟨b, lo, hi⟩
      change (match Mem.free m b lo hi with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m b lo hi with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          apply ih m1 m' tm
          · exact slp3_free_left_inject f m tm m1 b lo hi hinj hfm
          · exact hfree

theorem match_envs_free_blocks : match_envs_free_blocksStatement := by
  intro cfg p tp hprog
  dsimp only
  let ge := globalenv p
  let tge := globalenv tp
  intro j cenv e le m lo hi te tle tlo thi m' tm hme hinj hfree
  have hperms : ∀ b' lo' hi',
      (b', lo', hi') ∈ blocks_of_env tge te →
      Mem.range_perm tm b' lo' hi' .Cur .Freeable := by
    intro b' lo' hi' hmem
    unfold blocks_of_env at hmem
    rcases List.mem_map.mp hmem with ⟨q, hq, heq⟩
    rcases q with ⟨id, bty⟩
    rcases bty with ⟨b, ty⟩
    simp [block_of_binding] at heq
    rcases heq with ⟨hb, hlo, hhi⟩
    have hte : PTree.get id te = some (b, ty) :=
      PTree.elements_complete_proof te id (b, ty) hq
    rcases hme.me_mapped id b ty hte with ⟨b0, hmap, hget⟩
    have hrange := free_blocks_of_env_perm_2 ge m e m' id b0 ty hfree hget
    subst b'
    subst lo'
    subst hi'
    have henv : tge.genv_cenv = ge.genv_cenv := by
      exact comp_env_preserved cfg p tp hprog
    intro ofs hof
    have hof' : ZArith.BinInt.Z.le (.Z0 : Z) ofs ∧
        ZArith.BinInt.Z.lt ofs (sizeof ge.genv_cenv ty) := by
      rw [← henv]
      exact hof
    have hp := hrange ofs hof'
    have hpt := hinj.mi_inj.mi_perm b0 b .Z0 ofs .Cur .Freeable hmap hp
    change Mem.perm tm b (ZArith.BinInt.Z.add ofs (.Z0 : Z))
      .Cur .Freeable at hpt
    rw [mav_zadd_zero] at hpt
    exact hpt
  have hno : freelist_no_overlap (blocks_of_env tge te) := by
    rw [blocks_of_env_translated cfg p tp hprog te]
    unfold blocks_of_env
    apply blocks_of_env_no_overlap ge j cenv e le m lo hi te tle tlo thi tm
      hme hinj
      (fun id b ty hget => free_blocks_of_env_perm_2 ge m e m' id b ty hfree hget)
      (PTree.elements te) (PTree.elements_keys_norepet te)
    intro id bty hmem
    exact PTree.elements_complete_proof te id bty hmem
  rcases can_free_list (blocks_of_env tge te) tm hperms hno with ⟨tm', hfree'⟩
  refine ⟨tm', hfree', ?_⟩
  have hinj' : Mem.inject j m' tm :=
    slp3_free_list_left_inject j (blocks_of_env ge e) m m' tm hinj hfree
  apply free_list_right_inject j m' (blocks_of_env tge te) tm tm' hinj' hfree'
  intro b1 b2 delta lo' hi' ofs k permission hmap hmem hp hinside
  unfold blocks_of_env at hmem
  rcases List.mem_map.mp hmem with ⟨q, hq, heq⟩
  rcases q with ⟨id, bty⟩
  rcases bty with ⟨b, ty⟩
  simp [block_of_binding] at heq
  rcases heq with ⟨hb, hlo, hhi⟩
  subst b2
  subst lo'
  subst hi'
  have hte : PTree.get id te = some (b, ty) :=
    PTree.elements_complete_proof te id (b, ty) hq
  rcases hme.me_flat id b ty b1 delta hte hmap with ⟨hget, hdelta⟩
  subst delta
  apply free_blocks_of_env_perm_1 ge m e m' id b1 ty ofs k permission hfree hget hp
  have henv : tge.genv_cenv = ge.genv_cenv := by
    exact comp_env_preserved cfg p tp hprog
  rw [← henv]
  change ZArith.BinInt.Z.le (.Z0 : Z) ofs ∧
    ZArith.BinInt.Z.lt ofs (sizeof tge.genv_cenv ty)
  have hzadd : ZArith.BinInt.Z.add ofs (.Z0 : Z) = ofs := mav_zadd_zero ofs
  rw [hzadd] at hinside
  exact hinside

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

theorem match_globalenvs_preserves_globals :
    match_globalenvs_preserves_globalsStatement := by
  intro prog f h
  rcases h with ⟨bound, hmg⟩
  rcases hmg with ⟨hdom, himage, hsymbols, hfunctions, hvarinfos⟩
  constructor
  · intro id b hfind
    exact hdom b (hsymbols id b hfind)
  constructor
  · intro b gv hfind
    exact hdom b (hvarinfos b gv hfind)
  · intro b1 b2 delta gv hfind hmap
    exact (himage b1 b2 delta hmap (hvarinfos b2 gv hfind)).symm

theorem typeof_simpl_expr : typeof_simpl_exprStatement := by
  intro cenv a
  cases a <;> try rfl
  case Evar id ty =>
    by_cases h : VSet.mem id cenv = true <;>
      simp [simpl_expr, typeof, h]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib

theorem match_cont_invariant : match_cont_invariantStatement := by
  intro cfg prog f' m' f cenv k tk m bound tbound hmatch hload hincr hsource htarget
  induction hmatch with
  | stop cenv m bound tbound hi hglobals hhibound hhitbound =>
      apply match_cont.stop
      · cases hglobals with
        | intro hdomain himage hsymbols hfunctions hvarinfos =>
            exact match_globalenvs.intro
              (fun b hb => hincr b b (.Z0 : Z) (hdomain b hb))
              (fun b1 b2 delta hmap hb2 => by
                have hb2' : Plt b2 tbound := Nat.lt_of_lt_of_le hb2 hhitbound
                have heq := htarget b1 b2 delta hmap hb2'
                apply himage b1 b2 delta
                · rw [← heq]
                  exact hmap
                · exact hb2)
              hsymbols hfunctions hvarinfos
      · exact hhibound
      · exact hhitbound
  | seq cenv s k ts tk m bound tbound hstmt hcont hcompat ih =>
      exact match_cont.seq cenv s k ts tk m' bound tbound hstmt
        (ih hload hsource htarget) hcompat
  | loop1 cenv s1 s2 k ts1 ts2 tk m bound tbound hstmt1 hstmt2 hcont hcompat ih =>
      exact match_cont.loop1 cenv s1 s2 k ts1 ts2 tk m' bound tbound hstmt1 hstmt2
        (ih hload hsource htarget) hcompat
  | loop2 cenv s1 s2 k ts1 ts2 tk m bound tbound hstmt1 hstmt2 hcont hcompat ih =>
      exact match_cont.loop2 cenv s1 s2 k ts1 ts2 tk m' bound tbound hstmt1 hstmt2
        (ih hload hsource htarget) hcompat
  | switch cenv k tk m bound tbound hcont ih =>
      exact match_cont.switch cenv k tk m' bound tbound
        (ih hload hsource htarget)
  | match_Kcall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x
      hfun henv hcont hcheck hhibound hthitbound ih =>
      have hlohi : Ple lo hi := henv.me_incr
      have htlohi : Ple tlo thi := henv.me_tincr
      apply match_cont.match_Kcall cenv optid fn e le k tfn te tle tk m'
        hi thi lo tlo bound tbound x hfun
      · apply match_envs_invariant f (cenv_for fn) e le m lo hi te tle tlo thi f' m'
          henv
        · intro b chunk v hnone hb hmem
          apply hload b chunk v hnone
          · exact Nat.lt_of_lt_of_le hb.2 hhibound
          · exact hmem
        · exact hincr
        · intro b hb
          exact hsource b (Nat.lt_of_lt_of_le hb.2 hhibound)
        · intro b b' delta hmap hb'
          exact htarget b b' delta hmap (Nat.lt_of_lt_of_le hb'.2 hthitbound)
      · apply ih
        · intro b chunk v hnone hb hmem
          apply hload b chunk v hnone
          · exact Nat.lt_of_lt_of_le hb (Nat.le_trans hlohi hhibound)
          · exact hmem
        · intro b hb
          exact hsource b (Nat.lt_of_lt_of_le hb (Nat.le_trans hlohi hhibound))
        · intro b b' delta hmap hb'
          exact htarget b b' delta hmap
            (Nat.lt_of_lt_of_le hb' (Nat.le_trans htlohi hthitbound))
      · exact hcheck
      · exact hhibound
      · exact hthitbound

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Lib.Coqlib

theorem match_cont_assign_loc : match_cont_assign_locStatement := by
  intro cfg prog f cenv k tk m bound tbound ty loc ofs bf v m' hmatch hassign hloc
  apply match_cont_invariant cfg prog f m' f cenv k tk m bound tbound hmatch
  · intro b chunk value hnone hblt hmem
    have hne : b ≠ loc := by
      intro heq
      subst b
      exact (Nat.not_lt_of_ge hloc) hblt
    cases hassign with
    | assign_loc_value value' chunk' m' hmode hstore =>
        simp [Mem.storev] at hstore
        rw [Mem.load_store_other chunk' m loc
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) v m' hstore
          chunk b (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (Or.inl hne)]
        exact hmem
    | assign_loc_copy source sourceOfs bytes m' hmode halignSource halignTarget
        hseparated hbytes hstore =>
        rw [Mem.load_storebytes_other m loc
          (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs) bytes m' hstore
          chunk b (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (Or.inl hne)]
        exact hmem
    | assign_loc_bitfield sz sg pos width value' m' result hstore =>
        cases hstore with
        | store_bitfield_intro sz sg1 attr sg pos width m addr c n m'
            hpos hwidth hcarrier hsg hload hstore =>
            simp [Mem.storev] at hstore
            rw [Mem.load_store_other (chunk_for_carrier sz) m loc
              (CompCert4Lean.Lib.Integers.Ptrofs.unsigned ofs)
              (.Vint (CompCert4Lean.Lib.Integers.Int.bitfield_insert
                (first_bit sz pos width) width c n)) m' hstore
              chunk b (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) (Or.inl hne)]
            exact hmem
  · exact CompCert4Lean.Common.Values.inject_incr_refl f
  · intro b hb
    rfl
  · intro b b' delta hmap hb'
    rfl

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Lib.Coqlib

theorem match_cont_incr_bounds : match_cont_incr_boundsStatement := by
  intro cfg prog f cenv k tk m bound tbound hmatch bound' tbound'
  induction hmatch generalizing bound' tbound' with
  | stop cenv m bound tbound hi hglobals hhibound hthitbound =>
      intro hbound htbound
      exact match_cont.stop cenv m bound' tbound' hi hglobals
        (Ple_trans hi bound bound' hhibound hbound)
        (Ple_trans hi tbound tbound' hthitbound htbound)
  | seq cenv s k ts tk m bound tbound hstmt hcont hcompat ih =>
      intro hbound htbound
      exact match_cont.seq cenv s k ts tk m bound' tbound' hstmt
        (ih bound' tbound' hbound htbound) hcompat
  | loop1 cenv s1 s2 k ts1 ts2 tk m bound tbound hstmt1 hstmt2 hcont hcompat ih =>
      intro hbound htbound
      exact match_cont.loop1 cenv s1 s2 k ts1 ts2 tk m bound' tbound' hstmt1 hstmt2
        (ih bound' tbound' hbound htbound) hcompat
  | loop2 cenv s1 s2 k ts1 ts2 tk m bound tbound hstmt1 hstmt2 hcont hcompat ih =>
      intro hbound htbound
      exact match_cont.loop2 cenv s1 s2 k ts1 ts2 tk m bound' tbound' hstmt1 hstmt2
        (ih bound' tbound' hbound htbound) hcompat
  | switch cenv k tk m bound tbound hcont ih =>
      intro hbound htbound
      exact match_cont.switch cenv k tk m bound' tbound'
        (ih bound' tbound' hbound htbound)
  | match_Kcall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x
      hfun henv hcont hcheck hhibound hthitbound ih =>
      intro hbound htbound
      exact match_cont.match_Kcall cenv optid fn e le k tfn te tle tk m
        hi thi lo tlo bound' tbound' x hfun henv
        (ih lo tlo (Ple_refl lo) (Ple_refl tlo)) hcheck
        (Ple_trans hi bound bound' hhibound hbound)
        (Ple_trans thi tbound tbound' hthitbound htbound)

theorem match_cont_change_cenv : match_cont_change_cenvStatement := by
  intro cfg prog f cenv k tk m bound tbound cenv' hmatch hcall
  cases hmatch <;> simp [is_call_cont] at hcall ⊢ <;>
    try contradiction
  all_goals constructor <;> assumption

theorem match_cont_is_call_cont : match_cont_is_call_contStatement := by
  intro cfg prog f cenv k tk m bound tbound hmatch hcall
  cases hmatch <;> simp [is_call_cont] at hcall ⊢ <;>
    try contradiction
  all_goals assumption

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem slp_intOfZ_zadd (x y : Z) :
    intOfZ (ZArith.BinInt.Z.add x y) = intOfZ x + intOfZ y := by
  change intOfZ (zOfInt (intOfZ x + intOfZ y)) = intOfZ x + intOfZ y
  rw [intOfZ_zOfInt]

private theorem slp_zadd_lt (x y : Z)
    (hy : ZArith.BinInt.Z.lt (.Z0 : Z) y) :
    ZArith.BinInt.Z.lt x (ZArith.BinInt.Z.add x y) := by
  change intOfZ x < intOfZ (ZArith.BinInt.Z.add x y)
  rw [slp_intOfZ_zadd]
  change 0 < intOfZ y at hy
  omega

private theorem slp_load_unchanged_on
    (P : block → Z → Prop) (m m' : mem) (chunk : memory_chunk)
    (b : block) (p : Z) (v : val)
    (hunch : Mem.unchanged_on P m m')
    (hP : ∀ i, ZArith.BinInt.Z.le p i ∧
      ZArith.BinInt.Z.lt i
        (ZArith.BinInt.Z.add p (size_chunk chunk)) → P b i)
    (hload : Mem.load chunk m b p = some v) :
    Mem.load chunk m' b p = some v := by
  have hvacc := Mem.load_valid_access m chunk b p v hload
  have hpvalid := hvacc.1 p ⟨by
    change intOfZ p ≤ intOfZ p
    omega, slp_zadd_lt p (size_chunk chunk)
      (CompCert4Lean.Common.Memdata.size_chunk_pos chunk)⟩
  have hvb := Mem.perm_valid_block m b p Cur Readable hpvalid
  have hrange : Mem.range_perm m' b p
      (ZArith.BinInt.Z.add p (size_chunk chunk)) Cur Readable := by
    intro q hq
    apply (hunch.unchanged_on_perm b q Cur Readable (hP q hq) hvb).mp
    exact hvacc.1 q hq
  have hvalid' : Mem.valid_access m' chunk b p Readable := ⟨hrange, hvacc.2⟩
  have hgetN :
      Mem.getN (size_chunk_nat chunk) p (PMap.get b m'.mem_contents) =
        Mem.getN (size_chunk_nat chunk) p (PMap.get b m.mem_contents) := by
    apply Mem.getN_exten
    intro q hq
    apply hunch.unchanged_on_contents b q
    · apply hP q
      constructor
      · exact hq.1
      · have hsize := CompCert4Lean.Common.Memdata.size_chunk_conv chunk
        simpa [hsize] using hq.2
    · apply hvacc.1 q
      constructor
      · exact hq.1
      · have hsize := CompCert4Lean.Common.Memdata.size_chunk_conv chunk
        simpa [hsize] using hq.2
  rcases Mem.valid_access_load m' chunk b p hvalid' with ⟨v', hload'⟩
  have hres' := Mem.load_result chunk m' b p v' hload'
  have hres := Mem.load_result chunk m b p v hload
  have heq : v' = v := by
    calc
      v' = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) p (PMap.get b m'.mem_contents)) := hres'
      _ = decode_val chunk
          (Mem.getN (size_chunk_nat chunk) p (PMap.get b m.mem_contents)) := by rw [hgetN]
      _ = v := hres.symm
  simpa [heq] using hload'

theorem match_cont_extcall : match_cont_extcallStatement := by
  intro cfg prog f cenv k tk m bound tbound tm f' m' hmatch hunch hincr hsep hbound htbound
  apply match_cont_invariant cfg prog f' m' f cenv k tk m bound tbound hmatch
  · intro b chunk v hnone hb hload
    apply slp_load_unchanged_on (loc_unmapped f) m m' chunk b (.Z0 : Z) v hunch
    · intro i hi
      exact hnone
    · exact hload
  · exact hincr
  · intro b hb
    by_cases hf : f b = none
    · cases hfp : f' b with
      | none => exact hf.symm
      | some pair =>
        rcases pair with ⟨b', delta⟩
        have hmap : f' b = some (b', delta) := hfp
        have hvb : Mem.valid_block m b := by
          exact Plt_Ple_trans b bound m.nextblock hb hbound
        exact False.elim ((hsep b b' delta hf hmap).1 hvb)
    · cases hff : f b with
      | none => exact False.elim (hf hff)
      | some pair =>
        rcases pair with ⟨b', delta⟩
        exact hincr b b' delta hff
  · intro b b' delta hmap hb'
    by_cases hf : f b = none
    · have hvb' : Mem.valid_block tm b' :=
        Plt_Ple_trans b' tbound tm.nextblock hb' htbound
      exact False.elim ((hsep b b' delta hf hmap).2 hvb')
    · cases hff : f b with
      | none => exact False.elim (hf hff)
      | some pair =>
        rcases pair with ⟨b0, delta0⟩
        exact hincr b b0 delta0 hff

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem match_cont_call_cont : match_cont_call_contStatement := by
  intro cfg prog f cenv k tk m bound tbound hmatch
  induction hmatch with
  | stop cenv m bound tbound hi hglobals hhibound hthitbound =>
      intro cenv'
      simp [CompCert4Lean.Cfrontend.Clight.call_cont]
      exact match_cont.stop cenv' m bound tbound hi hglobals hhibound hthitbound
  | seq cenv s k ts tk m bound tbound hstmt hcont hcompat ih =>
      intro cenv'
      simpa [CompCert4Lean.Cfrontend.Clight.call_cont] using ih cenv'
  | loop1 cenv s1 s2 k ts1 ts2 tk m bound tbound hstmt1 hstmt2 hcont hcompat ih =>
      intro cenv'
      simpa [CompCert4Lean.Cfrontend.Clight.call_cont] using ih cenv'
  | loop2 cenv s1 s2 k ts1 ts2 tk m bound tbound hstmt1 hstmt2 hcont hcompat ih =>
      intro cenv'
      simpa [CompCert4Lean.Cfrontend.Clight.call_cont] using ih cenv'
  | switch cenv k tk m bound tbound hcont ih =>
      intro cenv'
      simpa [CompCert4Lean.Cfrontend.Clight.call_cont] using ih cenv'
  | match_Kcall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x
      hfun henv hcont hcheck hhibound hthitbound ih =>
      intro cenv'
      simpa [CompCert4Lean.Cfrontend.Clight.call_cont] using
        (match_cont.match_Kcall cenv' optid fn e le k tfn te tle tk m
          hi thi lo tlo bound tbound x hfun henv hcont hcheck hhibound hthitbound)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory

theorem free_list_nextblock : free_list_nextblockStatement := by
  intro l
  induction l with
  | nil =>
      intro m m' hfree
      simp [Mem.free_list] at hfree
      cases hfree
      rfl
  | cons x rest ih =>
      intro m m' hfree
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          have hnext : m'.nextblock = m1.nextblock := ih m1 m' hrest
          exact hnext.trans (slp3_nextblock_free m x.1 x.2.1 x.2.2 m1 hfm)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Coqlib

theorem free_list_load : free_list_loadStatement := by
  intro chunk b' l
  induction l with
  | nil =>
      intro m m' hfree hlt
      simp [Mem.free_list] at hfree
      cases hfree
      rfl
  | cons x rest ih =>
      intro m m' hfree hlt
      change (match Mem.free m x.1 x.2.1 x.2.2 with
        | none => none
        | some m1 => Mem.free_list m1 rest) = some m' at hfree
      cases hfm : Mem.free m x.1 x.2.1 x.2.2 with
      | none =>
          rw [hfm] at hfree
          cases hfree
      | some m1 =>
          rw [hfm] at hfree
          have hrest : Mem.free_list m1 rest = some m' := hfree
          have hnext : Mem.load chunk m' b' (.Z0 : Z) =
              Mem.load chunk m1 b' (.Z0 : Z) := ih m1 m' hrest (by
                intro b lo hi hin
                exact hlt b lo hi (List.mem_cons.mpr (Or.inr hin)))
          have hone : Mem.load chunk m1 b' (.Z0 : Z) =
              Mem.load chunk m b' (.Z0 : Z) :=
            Mem.load_free m x.1 x.2.1 x.2.2 m1 hfm chunk b' (.Z0 : Z)
              (Or.inl (Plt_ne b' x.1 (hlt x.1 x.2.1 x.2.2
                (List.mem_cons.mpr (Or.inl rfl)))))
          exact hnext.trans hone

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Memory
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Lib.Coqlib

open CompCert4Lean.Lib.Maps

theorem match_cont_free_env : match_cont_free_envStatement := by
  intro cfg prog tprog
  dsimp
  intro f cenv e le m lo hi te tle tm tlo thi k tk m' tm'
    henv hcont hhi hthi hfree hfree'
  apply match_cont_incr_bounds cfg prog f cenv k tk m' lo tlo
  · apply match_cont_invariant cfg prog f m' f cenv k tk m lo tlo hcont
    · intro b chunk v hnone hb hload
      calc
        Mem.load chunk m' b (.Z0 : Z) = Mem.load chunk m b (.Z0 : Z) := by
          apply free_list_load chunk b (blocks_of_env (globalenv prog) e) m m'
            hfree
          intro b0 lo0 hi0 hmem
          unfold blocks_of_env at hmem
          rcases List.mem_map.mp hmem with ⟨id_b_ty, hel, heq⟩
          rcases id_b_ty with ⟨id, b0', ty⟩
          simp [block_of_binding] at heq
          have hb0 : b0' = b0 := heq.1
          subst b0'
          have hget := PTree.elements_complete_proof e id (b0, ty) hel
          exact Plt_Ple_trans b lo b0 (by exact hb) (henv.me_range id b0 ty hget).1
        _ = some v := hload
    · exact CompCert4Lean.Common.Values.inject_incr_refl f
    · intro b hb
      rfl
    · intro b b' delta hmap hb'
      rfl
  · have hmnext := free_list_nextblock _ m m' hfree
    rw [hmnext]
    exact Ple_trans lo hi m.nextblock henv.me_incr hhi
  · have htmnext := free_list_nextblock _ tm tm' hfree'
    rw [htmnext]
    exact Ple_trans tlo thi tm.nextblock henv.me_tincr hthi

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem match_cont_globalenv : match_cont_globalenvStatement := by
  intro cfg prog f cenv k tk m bound tbound h
  induction h with
  | stop cenv m bound tbound hi hmg hbound htb =>
      exact ⟨hi, hmg⟩
  | seq cenv s k ts tk m bound tbound hs hprev hcompat ih => exact ih
  | loop1 cenv s1 s2 k ts1 ts2 tk m bound tbound hs1 hs2 hprev hcompat ih => exact ih
  | loop2 cenv s1 s2 k ts1 ts2 tk m bound tbound hs1 hs2 hprev hcompat ih => exact ih
  | switch cenv k tk m bound tbound hprev ih => exact ih
  | match_Kcall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x htf henv hprev hop hbound htb ih => exact ih

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.SimplLocals

theorem is_liftable_var_charact : is_liftable_var_charactStatement := by
  intro cenv a
  cases a with
  | Evar id ty =>
      unfold CompCert4Lean.Cfrontend.SimplLocals.is_liftable_var
      cases hmem : VSet.mem id cenv with
      | true => simp [hmem]
      | false => simp [hmem]
  | _ => simp [CompCert4Lean.Cfrontend.SimplLocals.is_liftable_var]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

theorem simpl_select_switch : simpl_select_switchStatement := by
  intro cfg cenv n ls tls h
  have DFL : ∀ ls tls,
      simpl_lblstmt cfg cenv ls = .OK tls →
        simpl_lblstmt cfg cenv (select_switch_default ls) =
          .OK (select_switch_default tls) := by
    let P0 : labeled_statements → Prop := fun ls =>
      ∀ tls, simpl_lblstmt cfg cenv ls = .OK tls →
        simpl_lblstmt cfg cenv (select_switch_default ls) =
          .OK (select_switch_default tls)
    have H : ∀ ls, P0 ls := by
      apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec
        (motive_1 := fun _ => True) (motive_2 := P0)
      all_goals try simp
      case LSnil =>
        intro tls h
        cases h
        rfl
      case LScons =>
        intro case stmt rest ih tls h
        simp only [simpl_lblstmt] at h
        split at h <;> try contradiction
        rename_i hstmt
        split at h <;> try contradiction
        rename_i hrest
        cases h
        cases case with
        | none =>
            simp [select_switch_default, simpl_lblstmt, hstmt, hrest]
        | some c =>
            simp only [select_switch_default]
            exact ih _ hrest
    exact H
  have CASE : ∀ ls tls,
      simpl_lblstmt cfg cenv ls = .OK tls →
      match select_switch_case n ls with
      | none => select_switch_case n tls = none
      | some ls' =>
          ∃ tls', select_switch_case n tls = some tls' ∧
            simpl_lblstmt cfg cenv ls' = .OK tls' := by
    let P0 : labeled_statements → Prop := fun ls =>
      ∀ tls, simpl_lblstmt cfg cenv ls = .OK tls →
        match select_switch_case n ls with
        | none => select_switch_case n tls = none
        | some ls' =>
            ∃ tls', select_switch_case n tls = some tls' ∧
              simpl_lblstmt cfg cenv ls' = .OK tls'
    have H : ∀ ls, P0 ls := by
      apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec
        (motive_1 := fun _ => True) (motive_2 := P0)
      all_goals try simp
      case LSnil =>
        intro tls h
        cases h
        rfl
      case LScons =>
        intro case stmt rest ih tls h
        simp only [simpl_lblstmt] at h
        split at h <;> try contradiction
        rename_i hstmt
        split at h <;> try contradiction
        rename_i hrest
        cases h
        cases case with
        | none =>
            simpa [select_switch_case] using ih _ hrest
        | some c =>
            cases hz : CompCert4Lean.Lib.Coqlib.zeq c n with
            | left heq =>
                simp only [select_switch_case, hz]
                refine ⟨_, rfl, ?_⟩
                simp only [simpl_lblstmt, hstmt, hrest]
            | right hne =>
                simpa [select_switch_case, hz] using ih _ hrest
    exact H
  have hcase := CASE ls tls h
  cases hs : select_switch_case n ls with
  | some ls' =>
      have hcase' : ∃ tls', select_switch_case n tls = some tls' ∧
          simpl_lblstmt cfg cenv ls' = .OK tls' := by
        simpa [hs] using hcase
      rcases hcase' with ⟨tls', htarget, hls'⟩
      simp [select_switch, hs, htarget, hls']
  | none =>
      have hcase' : select_switch_case n tls = none := by
        simpa [hs] using hcase
      simp [select_switch, hs, hcase']
      exact DFL _ _ h

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Integers

theorem match_cont_find_funct : match_cont_find_functStatement := by
  intro cfg p tp hprog f cenv k tk m bound tbound vf fd tvf hcont hfind hinj
  have htrans := @Genv.find_funct_transf_partial
    (CompCert4Lean.Cfrontend.Ctypes.fundef function)
    (CompCert4Lean.Cfrontend.Ctypes.fundef function) type _ _
    (transf_fundef cfg) (program_of_program p) (program_of_program tp)
    hprog.1 vf fd hfind
  rcases htrans with ⟨tfd, htfind, htf⟩
  have hgenv := match_cont_globalenv cfg p f cenv k tk m bound tbound hcont
  rcases hgenv with ⟨bound', hmg⟩
  cases vf with
  | Vundef => simp [Genv.find_funct] at hfind
  | Vint n => simp [Genv.find_funct] at hfind
  | Vlong n => simp [Genv.find_funct] at hfind
  | Vfloat n => simp [Genv.find_funct] at hfind
  | Vsingle n => simp [Genv.find_funct] at hfind
  | Vptr b ofs =>
      unfold Genv.find_funct at hfind
      cases hzero : Ptrofs.eq ofs Ptrofs.zero with
      | false => simp [hzero] at hfind
      | true =>
          have hptr : Genv.find_funct_ptr
              (Genv.globalenv (program_of_program p)) b = some fd := by
            simpa [hzero] using hfind
          cases hmg with
          | intro hdomain himage hsymbols hfunctions hvarinfos =>
              have hmap : f b = some (b, .Z0) :=
                hdomain b (hfunctions b fd hptr)
              cases hinj with
              | inject_ptr b1 ofs1 b2 ofs2 delta hfb hofs =>
                  rw [hmap] at hfb
                  cases hfb
                  have hofsz : ofs = Ptrofs.zero := by
                    unfold Ptrofs.eq CompCert4Lean.Lib.Integers.WordCore.eq at hzero
                    exact CompCert4Lean.Lib.Integers.WordCore.ext
                      (of_decide_eq_true hzero)
                  subst ofs
                  have hadd : Ptrofs.add Ptrofs.zero (Ptrofs.repr (.Z0)) =
                      Ptrofs.zero := by
                    have hrepr : Ptrofs.repr (.Z0) = Ptrofs.zero := by rfl
                    have huns : Ptrofs.unsigned Ptrofs.zero = (.Z0) := by rfl
                    have hrepr_core :
                        CompCert4Lean.Lib.Integers.WordCore.repr
                            Ptrofs.wordsize (.Z0) =
                          CompCert4Lean.Lib.Integers.WordCore.zero
                            Ptrofs.wordsize := by rfl
                    have huns_repr :
                        CompCert4Lean.Lib.Integers.WordCore.unsigned
                            (CompCert4Lean.Lib.Integers.WordCore.repr
                              Ptrofs.wordsize (.Z0)) = (.Z0) := by rfl
                    apply CompCert4Lean.Lib.Integers.WordCore.ext
                    change Ptrofs.unsigned
                      (Ptrofs.add Ptrofs.zero (Ptrofs.repr (.Z0))) =
                      Ptrofs.unsigned Ptrofs.zero
                    rw [hrepr]
                    simp [Ptrofs.unsigned, Ptrofs.add, Ptrofs.zero, Ptrofs.repr,
                      CompCert4Lean.Lib.Integers.WordCore.add,
                      CompCert4Lean.Lib.Integers.WordCore.zero, huns,
                      huns_repr]
                    change CompCert4Lean.Lib.Integers.WordCore.unsigned
                      (CompCert4Lean.Lib.Integers.WordCore.repr
                        Ptrofs.wordsize (.Z0)) = (.Z0)
                    exact huns_repr
                  have hofs0 : ofs2 = Ptrofs.zero := by
                    simpa [hadd] using hofs
                  subst ofs2
                  exact ⟨tfd, htfind, htf⟩

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

theorem compat_cenv_select_switch : compat_cenv_select_switchStatement := by
  intro cenv n
  have DFL : ∀ ls,
      compat_cenv (addr_taken_lblstmt ls) cenv →
        compat_cenv (addr_taken_lblstmt (select_switch_default ls)) cenv := by
    let P0 : labeled_statements → Prop := fun ls =>
      compat_cenv (addr_taken_lblstmt ls) cenv →
        compat_cenv (addr_taken_lblstmt (select_switch_default ls)) cenv
    have H : ∀ ls, P0 ls := by
      apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec
        (motive_1 := fun _ => True) (motive_2 := P0)
      all_goals try simp
      case LSnil => intro h; exact compat_cenv_empty cenv
      case LScons =>
        intro case stmt rest ih h
        cases case with
        | none => simpa [select_switch_default] using h
        | some c => exact ih (compat_union_right _ _ _ h)
    exact H
  have CASE : ∀ ls ls',
      compat_cenv (addr_taken_lblstmt ls) cenv →
      select_switch_case n ls = some ls' →
      compat_cenv (addr_taken_lblstmt ls') cenv := by
    let P0 : labeled_statements → Prop := fun ls =>
      ∀ ls', compat_cenv (addr_taken_lblstmt ls) cenv →
        select_switch_case n ls = some ls' →
        compat_cenv (addr_taken_lblstmt ls') cenv
    have H : ∀ ls, P0 ls := by
      apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec
        (motive_1 := fun _ => True) (motive_2 := P0)
      all_goals try simp
      case LSnil =>
        intro ls' _ h
        simp [select_switch_case] at h
      case LScons =>
        intro case stmt rest ih ls' h hsel
        cases case with
        | none => exact ih ls' (compat_union_right _ _ _ h) hsel
        | some c =>
            cases hz : CompCert4Lean.Lib.Coqlib.zeq c n with
            | left heq =>
                simp only [select_switch_case, hz] at hsel
                cases hsel
                simpa [addr_taken_lblstmt] using h
            | right hne =>
                apply ih ls' (compat_union_right _ _ _ h)
                simpa [select_switch_case, hz] using hsel
    exact H
  intro ls h
  cases hs : select_switch_case n ls with
  | some ls' =>
      simp [select_switch, hs]
      exact CASE ls ls' h hs
  | none =>
      simp [select_switch, hs]
      exact DFL ls h

theorem addr_taken_seq_of_labeled_statement : addr_taken_seq_of_labeled_statementStatement := by
  intro ls
  let P : statement → Prop := fun _ => True
  let P0 : labeled_statements → Prop := fun ls =>
    addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls
  have H : ∀ ls, P0 ls := by
    apply CompCert4Lean.Cfrontend.Clight.labeled_statements.rec
      (motive_1 := P) (motive_2 := P0)
    all_goals try simp [P]
    case LSnil => rfl
    case LScons =>
      intro case stmt rest ih
      change VSet.union (addr_taken_stmt stmt)
          (addr_taken_stmt (seq_of_labeled_statement rest)) =
        VSet.union (addr_taken_stmt stmt) (addr_taken_lblstmt rest)
      rw [ih]
  exact H ls

theorem simpl_find_label : simpl_find_labelStatement := by
  intro cfg prog f cenv m bound tbound lbl
  let P : statement → Prop := fun s =>
    ∀ k ts tk, simpl_stmt cfg cenv s = .OK ts →
      match_cont cfg prog f cenv k tk m bound tbound →
      compat_cenv (addr_taken_stmt s) cenv →
      match find_label lbl s k with
      | none => find_label lbl ts tk = none
      | some (s', k') => ∃ ts' tk', find_label lbl ts tk = some (ts', tk') ∧
          compat_cenv (addr_taken_stmt s') cenv ∧ simpl_stmt cfg cenv s' = .OK ts' ∧
          match_cont cfg prog f cenv k' tk' m bound tbound
  have H : ∀ s, P s := by
    apply CompCert4Lean.Cfrontend.Clight.statement.rec
      (motive_1 := P) (motive_2 := fun _ => True)
    case Sskip =>
      intro k ts tk h _ _
      cases h
      rfl
    case Sassign =>
      intro lhs rhs k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h
      · cases h
        exact find_label_Sset_debug_none cfg lbl _ _ _ tk
      · cases h
        rfl
    case Sset =>
      intro id rhs k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Scall =>
      intro result fn args k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Sbuiltin =>
      intro result ef argTypes args k ts tk h _ _
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      cases h
      rfl
    case Ssequence =>
      intro s1 s2 ih1 ih2 k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i h1
      split at h <;> try contradiction
      rename_i h2
      cases h
      have compat1 : compat_cenv (addr_taken_stmt s1) cenv :=
        compat_union_left _ _ _ compat
      have compat2 : compat_cenv (addr_taken_stmt s2) cenv :=
        compat_union_right _ _ _ compat
      have mc1 := match_Kseq cenv s2 k _ tk m bound tbound h2 mc compat2
      have h1' := ih1 (.Kseq s2 k) _ (.Kseq _ tk) h1 mc1 compat1
      cases e : find_label lbl s1 (.Kseq s2 k) with
      | none =>
          simp [e] at h1'
          simpa [find_label, e, h1'] using ih2 k _ tk h2 mc compat2
      | some found =>
          rcases (by simpa [e] using h1') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sloop =>
      intro body iter ihbody ihiter k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hbody
      split at h <;> try contradiction
      rename_i hiter
      cases h
      have compatbody : compat_cenv (addr_taken_stmt body) cenv :=
        compat_union_left _ _ _ compat
      have compatiter : compat_cenv (addr_taken_stmt iter) cenv :=
        compat_union_right _ _ _ compat
      have mcbody := match_Kloop1 cenv body iter k _ _ tk m bound tbound
        hbody hiter mc compat
      have hbody' := ihbody (.Kloop1 body iter k) _ (.Kloop1 _ _ tk)
        hbody mcbody compatbody
      cases e : find_label lbl body (.Kloop1 body iter k) with
      | none =>
          simp [e] at hbody'
          have mciter := match_Kloop2 cenv body iter k _ _ tk m bound tbound
            hbody hiter mc compat
          simpa [find_label, e, hbody'] using
            ihiter (.Kloop2 body iter k) _ (.Kloop2 _ _ tk) hiter mciter compatiter
      | some found =>
          rcases (by simpa [e] using hbody') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case Sbreak =>
      intro k ts tk h _ _
      cases h
      rfl
    case Scontinue =>
      intro k ts tk h _ _
      cases h
      rfl
    case Sreturn =>
      intro result k ts tk h _ _
      cases h
      rfl
    case Sswitch =>
      intro selector cases ihcases k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hcases
      cases h
      have compatcases : compat_cenv (addr_taken_lblstmt cases) cenv :=
        compat_union_right _ _ _ compat
      have mc' := match_Kswitch cenv k tk m bound tbound mc
      simpa [find_label] using
        (simpl_find_label_ls cfg prog f cenv m bound tbound lbl cases
          (.Kswitch k) _ (.Kswitch tk) hcases mc' compatcases)
    case Slabel =>
      intro l body ihbody k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i hbody
      cases h
      have compatbody : compat_cenv (addr_taken_stmt body) cenv := by
        simpa [addr_taken_stmt] using compat
      cases e : CompCert4Lean.Common.AST.ident_eq lbl l with
      | left heq =>
          simp only [find_label, e]
          exact ⟨_, tk, rfl, compatbody, hbody, mc⟩
      | right hne =>
          simpa [find_label, e] using ihbody k _ tk hbody mc compatbody
    case Sgoto =>
      intro l k ts tk h _ _
      cases h
      rfl
    case Sifthenelse =>
      intro cond s1 s2 ih1 ih2 k ts tk h mc compat
      simp only [simpl_stmt] at h
      split at h <;> try contradiction
      rename_i h1
      split at h <;> try contradiction
      rename_i h2
      cases h
      have compat12 : compat_cenv
          (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv :=
        compat_union_right _ _ _ compat
      have compat1 : compat_cenv (addr_taken_stmt s1) cenv :=
        compat_union_left _ _ _ compat12
      have compat2 : compat_cenv (addr_taken_stmt s2) cenv :=
        compat_union_right _ _ _ compat12
      have h1' := ih1 k _ tk h1 mc compat1
      cases e : find_label lbl s1 k with
      | none =>
          simp [e] at h1'
          simpa [find_label, e, h1'] using ih2 k _ tk h2 mc compat2
      | some found =>
          rcases (by simpa [e] using h1') with ⟨ts', tk', hfind, hc, hs, hm⟩
          simp only [find_label, e]
          exact ⟨ts', tk', by rw [hfind], hc, hs, hm⟩
    case LSnil => exact True.intro
    case LScons => intros; exact True.intro
  intro s k ts tk h mc compat
  exact H s k ts tk h mc compat

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

theorem find_label_store_params : find_label_store_paramsStatement := by
  intro lbl cenv s k params
  induction params with
  | nil => rfl
  | cons p params ih =>
      cases p with
      | mk id ty =>
          simp only [store_params]
          split
          · split <;> simp [find_label, ih]
          · simp [find_label, ih]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Driver.Compopts

theorem find_label_add_debug_vars : find_label_add_debug_varsStatement := by
  intro cfg lbl s k vars
  unfold add_debug_vars
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · rw [hd]
    induction vars with
    | nil => rfl
    | cons p vars ih =>
        cases p with
        | mk id ty =>
            simp only [List.foldr]
            simp [add_debug_var, Sdebug_var, find_label] at ih ⊢
            exact ih
  · simp [hd]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Driver.Compopts

theorem find_label_add_debug_params : find_label_add_debug_paramsStatement := by
  intro cfg lbl s k vars
  unfold add_debug_params
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · rw [hd]
    induction vars with
    | nil => rfl
    | cons p vars ih =>
        cases p with
        | mk id ty =>
            simp only [List.foldr]
            simp [add_debug_param, Sdebug_temp, find_label] at ih ⊢
            exact ih
  · simp [hd]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

 theorem function_ptr_translated : function_ptr_translatedStatement := by
  intro cfg p tp hmatch b fd hfind
  exact @Genv.find_funct_ptr_transf_partial
    (CompCert4Lean.Cfrontend.Ctypes.fundef function)
    (CompCert4Lean.Cfrontend.Ctypes.fundef function) type _ _
    (transf_fundef cfg) (program_of_program p) (program_of_program tp)
    hmatch.1 b fd hfind

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals

theorem final_states_simulation : final_states_simulationStatement := by
  intro cfg p S R result hmatch hfinal
  cases hfinal
  cases hmatch with
  | return_ v k m tv tk tm j hcont hmem hinj =>
      have hc := hcont VSet.empty
      cases hc
      cases hinj
      exact final_state.intro _ _

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib

private theorem simpllocals_initial_globals (p : program) (m : mem)
    (hmem : Genv.init_mem (program_of_program p) = some m) :
    match_globalenvs p (Mem.flat_inj m.nextblock) m.nextblock := by
  constructor
  · intro b hb
    unfold Mem.flat_inj
    cases h : plt b m.nextblock with
    | left _ => rfl
    | right hn => exact False.elim (hn hb)
  · intro b1 b2 delta hmap _
    unfold Mem.flat_inj at hmap
    split at hmap
    · cases hmap
      rfl
    · contradiction
  · intro id b hs
    exact Genv.find_symbol_not_fresh _ _ (program_of_program p) id b m hmem hs
  · intro b fd hf
    exact Genv.find_funct_ptr_not_fresh _ _ (program_of_program p) b fd m hmem hf
  · intro b gv hv
    exact Genv.find_var_info_not_fresh _ _ (program_of_program p) b gv m hmem hv

theorem initial_states_simulation : initial_states_simulationStatement := by
  intro cfg p tp hmatch S hinitial
  cases hinitial with
  | intro b fd m hmem hsym hfun htype =>
      obtain ⟨tfd, htfun, htrans⟩ := function_ptr_translated cfg p tp hmatch b fd hfun
      refine ⟨.Callstate tfd [] .Kstop m, ?_, ?_⟩
      · apply initial_state.intro b tfd m
        · exact @Genv.init_mem_transf_partial
            (CompCert4Lean.Cfrontend.Ctypes.fundef function)
            (CompCert4Lean.Cfrontend.Ctypes.fundef function) type _ _ (transf_fundef cfg)
            (program_of_program p) (program_of_program tp) hmatch.1 m hmem
        · have hmain : tp.prog_main = p.prog_main := hmatch.1.2.1
          rw [hmain]
          exact (symbols_preserved cfg p tp hmatch p.prog_main).trans hsym
        · exact htfun
        · exact (type_of_fundef_preserved cfg fd tfd htrans).trans htype
      · apply match_states.call fd [] .Kstop m tfd [] .Kstop m
          (Mem.flat_inj m.nextblock) [] type_int32s cc_default
        · exact htrans
        · intro cenv
          exact match_cont.stop cenv m m.nextblock m.nextblock m.nextblock
            (simpllocals_initial_globals p m hmem) (Ple_refl _) (Ple_refl _)
        · exact Genv.initmem_inject _ _ (program_of_program p) m hmem
        · constructor
        · exact htype
        · constructor

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem sl_link_tree_view {A : Type} (m : PTree.tree A) :
    ∃ l o r, m = PTree.Node l o r := by
  cases m with
  | Empty => exact ⟨.Empty, none, .Empty, rfl⟩
  | Nodes m =>
      cases m with
      | Node001 r => exact ⟨.Empty, none, .Nodes r, rfl⟩
      | Node010 x => exact ⟨.Empty, some x, .Empty, rfl⟩
      | Node011 x r => exact ⟨.Empty, some x, .Nodes r, rfl⟩
      | Node100 l => exact ⟨.Nodes l, none, .Empty, rfl⟩
      | Node101 l r => exact ⟨.Nodes l, none, .Nodes r, rfl⟩
      | Node110 l x => exact ⟨.Nodes l, some x, .Empty, rfl⟩
      | Node111 l x r => exact ⟨.Nodes l, some x, .Nodes r, rfl⟩

private theorem sl_link_elements {A B : Type} (R : A → B → Prop)
    (m1 : PTree.tree A) (m2 : PTree.tree B)
    (h : ∀ k, option_rel R (PTree.get k m1) (PTree.get k m2)) :
    list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2)
      (PTree.elements m1) (PTree.elements m2) := by
  have aux : ∀ m1 : PTree.tree A, ∀ m2 : PTree.tree B,
      (∀ k, option_rel R (PTree.get k m1) (PTree.get k m2)) →
      ∀ i, list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2)
        (PTree.xelements m1 i) (PTree.xelements m2 i) := by
    intro m1
    let P := fun m1 : PTree.tree A => PLift (∀ m2 : PTree.tree B,
      (∀ k, option_rel R (PTree.get k m1) (PTree.get k m2)) →
      ∀ i, list_forall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2)
        (PTree.xelements m1 i) (PTree.xelements m2 i))
    have proof : P m1 := by
      apply PTree.tree_ind P
      · refine ⟨?_⟩
        intro m2 hm i
        have he : m2 = .Empty := PTree.extensionality_empty m2 (by
          intro k
          have hk := hm k
          change option_rel R none (PTree.get k m2) at hk
          cases e : PTree.get k m2 with
          | none => rfl
          | some x => rw [e] at hk; cases hk)
        subst m2
        exact list_forall2.nil _
      · intro l ihl o r ihr _
        refine ⟨?_⟩
        intro m2 hm i
        obtain ⟨l2, o2, r2, rfl⟩ := sl_link_tree_view m2
        have hl : ∀ k, option_rel R (PTree.get k l) (PTree.get k l2) := by
          intro k
          have hk := hm (.xO k)
          rw [PTree.gNode_proof, PTree.gNode_proof] at hk
          exact hk
        have hr : ∀ k, option_rel R (PTree.get k r) (PTree.get k r2) := by
          intro k
          have hk := hm (.xI k)
          rw [PTree.gNode_proof, PTree.gNode_proof] at hk
          exact hk
        have ho : option_rel R o o2 := by
          have hk := hm .xH
          rw [PTree.gNode_proof, PTree.gNode_proof] at hk
          exact hk
        rw [PTree.xelements_Node, PTree.xelements_Node]
        apply list_forall2_app _ _ _ _ _ _ _
        · apply list_forall2_app _ _ _ _ _ _ _
          · exact ihl.down l2 hl _
          · cases ho with
            | none => exact list_forall2.nil _
            | some a b hab => exact list_forall2.cons _ _ ⟨rfl, hab⟩ (.nil _)
        · exact ihr.down r2 hr _
    exact proof.down
  exact aux m1 m2 h .xH

private theorem sl_link_fundef (cfg : CompilerConfig)
    (f1 f2 f tf1 tf2 : CompCert4Lean.Cfrontend.Ctypes.fundef function)
    (hl : CompCert4Lean.Cfrontend.Ctypes.link_fundef f1 f2 = some f)
    (h1 : CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f1 = .OK tf1)
    (h2 : CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f2 = .OK tf2) :
    ∃ tf, CompCert4Lean.Cfrontend.Ctypes.link_fundef tf1 tf2 = some tf ∧ CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf := by
  cases f1 with
  | Internal fn1 =>
      cases e1 : transf_function cfg fn1 with
      | Error msg => simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef, e1] at h1
      | OK tfn1 =>
          simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef, e1] at h1
          cases h1
          cases f2 with
          | Internal fn2 => simp [CompCert4Lean.Cfrontend.Ctypes.link_fundef] at hl
          | External ef args res cc =>
              cases h2
              cases ef <;> simp [CompCert4Lean.Cfrontend.Ctypes.link_fundef] at hl
              case EF_external id sg =>
                subst f
                exact ⟨.Internal tfn1, rfl, by simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef, e1]⟩
  | External ef args res cc =>
      cases h1
      cases f2 with
      | Internal fn2 =>
          cases e2 : transf_function cfg fn2 with
          | Error msg => simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef, e2] at h2
          | OK tfn2 =>
              simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef, e2] at h2
              cases h2
              cases ef <;> simp [CompCert4Lean.Cfrontend.Ctypes.link_fundef] at hl
              case EF_external id sg =>
                subst f
                exact ⟨.Internal tfn2, rfl, by simp [CompCert4Lean.Cfrontend.SimplLocals.transf_fundef, e2]⟩
      | External ef2 args2 res2 cc2 =>
          cases h2
          refine ⟨f, hl, ?_⟩
          simp only [CompCert4Lean.Cfrontend.Ctypes.link_fundef] at hl
          split at hl <;> try contradiction
          split at hl <;> try contradiction
          split at hl <;> try contradiction
          split at hl <;> try contradiction
          cases hl
          rfl

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private abbrev sl_link_ast :=
  CompCert4Lean.Common.AST.program (CompCert4Lean.Cfrontend.Ctypes.fundef function) type
private abbrev sl_link_global :=
  globdef (CompCert4Lean.Cfrontend.Ctypes.fundef function) type
private abbrev sl_link_match (cfg : CompilerConfig) (p : sl_link_ast) :
    sl_link_global → sl_link_global → Prop :=
  match_globdef (fun (_ : sl_link_ast) f tf =>
    CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf) Eq p

private theorem sl_link_context (cfg : CompilerConfig) (p q : sl_link_ast)
    (g tg : sl_link_global) (h : sl_link_match cfg p g tg) :
    sl_link_match cfg q g tg := by
  cases h with
  | match_globdef_fun ctx f tf _ ht =>
      exact match_globdef_fun _ _ _ q f tf (linkorder_refl q) ht
  | match_globdef_var v tv hv => exact match_globdef_var _ _ _ v tv hv

private theorem sl_link_variable {v tv : globvar type} (h : match_globvar Eq v tv) :
    v = tv := by
  cases h with
  | match_globvar_intro info tinfo init ro vo he => cases he; rfl

private theorem sl_link_globals (cfg : CompilerConfig) (p : sl_link_ast)
    (g1 g2 g tg1 tg2 : sl_link_global)
    (hl : link_def g1 g2 = some g)
    (h1 : sl_link_match cfg p g1 tg1) (h2 : sl_link_match cfg p g2 tg2) :
    ∃ tg, link_def tg1 tg2 = some tg ∧ sl_link_match cfg p g tg := by
  cases h1 with
  | match_globdef_fun ctx1 f1 tf1 _ ht1 =>
      cases h2 with
      | match_globdef_var v tv hv => cases hl
      | match_globdef_fun ctx2 f2 tf2 _ ht2 =>
          cases hf : Ctypes.link_fundef f1 f2 with
          | none => simp [link_def, Linker.link, Ctypes.Linker_fundef, hf] at hl
          | some f =>
              simp [link_def, Linker.link, Ctypes.Linker_fundef, hf] at hl
              subst g
              obtain ⟨tf, htf, ht⟩ := sl_link_fundef cfg f1 f2 f tf1 tf2 hf ht1 ht2
              refine ⟨.Gfun tf, ?_, ?_⟩
              · simp [link_def, Linker.link, Ctypes.Linker_fundef, htf]
              · exact match_globdef_fun _ _ _ p f tf (linkorder_refl p) ht
  | match_globdef_var v1 tv1 hv1 =>
      cases h2 with
      | match_globdef_fun ctx2 f2 tf2 _ ht2 => cases hl
      | match_globdef_var v2 tv2 hv2 =>
          have e1 := sl_link_variable hv1
          have e2 := sl_link_variable hv2
          subst tv1
          subst tv2
          refine ⟨g, hl, ?_⟩
          cases hv : link_vardef v1 v2 with
          | none => simp [link_def, hv] at hl
          | some v =>
              simp [link_def, hv] at hl
              subst g
              cases v
              exact match_globdef_var _ _ _ _ _
                (match_globvar_intro _ _ _ _ _ _ rfl)

private theorem sl_link_merge (cfg : CompilerConfig) (p : sl_link_ast)
    (o1 o2 t1 t2 : Option sl_link_global)
    (h1 : option_rel (sl_link_match cfg p) o1 t1)
    (h2 : option_rel (sl_link_match cfg p) o2 t2)
    (hl : ∀ g1 g2, o1 = some g1 → o2 = some g2 →
      ∃ g, link_def g1 g2 = some g) :
    option_rel (sl_link_match cfg p)
      (link_prog_merge o1 o2) (link_prog_merge t1 t2) := by
  cases h1 with
  | none => exact h2
  | some g1 tg1 hg1 =>
      cases h2 with
      | none => exact option_rel.some _ _ hg1
      | some g2 tg2 hg2 =>
          obtain ⟨g, hg⟩ := hl g1 g2 rfl rfl
          obtain ⟨tg, htg, hmatch⟩ := sl_link_globals cfg p g1 g2 g tg1 tg2 hg hg1 hg2
          simp only [link_prog_merge, hg, htg]
          exact option_rel.some _ _ hmatch

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

private theorem sl_link_some_left {A B : Type} {R : A → B → Prop} {x : A}
    {o : Option B} (h : option_rel R (some x) o) :
    ∃ y, o = some y ∧ R x y := by
  cases h with
  | some x y hr => exact ⟨y, rfl, hr⟩

private theorem sl_link_some_right {A B : Type} {R : A → B → Prop} {y : B}
    {o : Option A} (h : option_rel R o (some y)) :
    ∃ x, o = some x ∧ R x y := by
  cases h with
  | some x y hr => exact ⟨x, rfl, hr⟩

private theorem sl_link_none_left {A B : Type} {R : A → B → Prop}
    {o : Option B} (h : option_rel R none o) : o = none := by
  cases h
  rfl

private theorem sl_link_defmap (cfg : CompilerConfig) (p tp ctx : sl_link_ast)
    (h : match_program (fun (_ : sl_link_ast) (f tf : Ctypes.fundef function) =>
      CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf) Eq p tp)
    (k : ident) :
    option_rel (sl_link_match cfg ctx)
      (PTree.get k (prog_defmap p)) (PTree.get k (prog_defmap tp)) := by
  have hm := match_program_defmap
    (fun (_ : sl_link_ast) (f tf : Ctypes.fundef function) =>
      CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf)
    Eq p p tp h k
  generalize e1 : PTree.get k (prog_defmap p) = o1 at hm ⊢
  generalize e2 : PTree.get k (prog_defmap tp) = o2 at hm ⊢
  cases hm with
  | none => exact option_rel.none _
  | some g tg hr => exact option_rel.some _ _ (sl_link_context cfg p ctx g tg hr)

private theorem sl_link_ast_program (cfg : CompilerConfig)
    (p1 p2 tp1 tp2 p : sl_link_ast)
    (hl : link_prog p1 p2 = some p)
    (h1 : match_program (fun (_ : sl_link_ast) (f tf : Ctypes.fundef function) =>
      CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf) Eq p1 tp1)
    (h2 : match_program (fun (_ : sl_link_ast) (f tf : Ctypes.fundef function) =>
      CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf) Eq p2 tp2) :
    ∃ tp, link_prog tp1 tp2 = some tp ∧
      match_program (fun (_ : sl_link_ast) (f tf : Ctypes.fundef function) =>
        CompCert4Lean.Cfrontend.SimplLocals.transf_fundef cfg f = .OK tf) Eq p tp := by
  obtain ⟨hmain, hcompat, hp⟩ := link_prog_inv_proof p1 p2 p hl
  have hm1 := sl_link_defmap cfg p1 tp1 p h1
  have hm2 := sl_link_defmap cfg p2 tp2 p h2
  have hcheck : PTree_Properties.for_all (prog_defmap tp1)
      (link_prog_check tp1 tp2) = true := by
    apply (PTree_Properties.for_all_correct_proof _ _ _).mpr
    intro id tg1 ht1
    have hr1 := hm1 id
    rw [ht1] at hr1
    obtain ⟨g1, hg1, hr1⟩ := sl_link_some_right hr1
    cases hg2 : PTree.get id (prog_defmap p2) with
    | none =>
        have hr2 := hm2 id
        rw [hg2] at hr2
        have ht2 := sl_link_none_left hr2
        simp [link_prog_check, ht2]
    | some g2 =>
        have hr2 := hm2 id
        rw [hg2] at hr2
        obtain ⟨tg2, ht2, hr2⟩ := sl_link_some_left hr2
        obtain ⟨hpub1, hpub2, g, hg⟩ := hcompat id g1 g2 hg1 hg2
        obtain ⟨tg, htg, _⟩ := sl_link_globals cfg p g1 g2 g tg1 tg2 hg hr1 hr2
        have hpub1' : id ∈ tp1.prog_public := by rw [h1.2.2]; exact hpub1
        have hpub2' : id ∈ tp2.prog_public := by rw [h2.2.2]; exact hpub2
        simp only [link_prog_check, ht2]
        cases d1 : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
            peq id tp1.prog_public with
        | right hn => exact False.elim (hn hpub1')
        | left _ =>
            cases d2 : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                peq id tp2.prog_public with
            | right hn => exact False.elim (hn hpub2')
            | left _ => simp [htg]
  let tp : sl_link_ast :=
    { prog_main := tp1.prog_main
      prog_public := tp1.prog_public ++ tp2.prog_public
      prog_defs := PTree.elements
        (PTree.combine link_prog_merge (prog_defmap tp1) (prog_defmap tp2)) }
  refine ⟨tp, ?_, ?_⟩
  · unfold link_prog
    have htmain : tp1.prog_main = tp2.prog_main :=
      h1.2.1.trans (hmain.trans h2.2.1.symm)
    cases d : CompCert4Lean.Common.AST.ident_eq tp1.prog_main tp2.prog_main with
    | right hn => exact False.elim (hn htmain)
    | left _ => simp [hcheck, tp]
  · refine ⟨?_, ?_, ?_⟩
    · change list_forall2 (fun a b => a.1 = b.1 ∧ sl_link_match cfg p a.2 b.2)
        p.prog_defs tp.prog_defs
      rw [congrArg CompCert4Lean.Common.AST.program.prog_defs hp]
      apply sl_link_elements (sl_link_match cfg p)
      intro k
      rw [PTree.gcombine_proof (f := link_prog_merge) (by rfl),
        PTree.gcombine_proof (f := link_prog_merge) (by rfl)]
      apply sl_link_merge cfg p _ _ _ _ (hm1 k) (hm2 k)
      intro g1 g2 hg1 hg2
      exact (hcompat k g1 g2 hg1 hg2).2.2
    · simpa [tp, hp] using h1.2.1
    · simp [tp, hp, h1.2.2, h2.2.2]

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Linking
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes

private theorem sl_link_program_inv (certificate : Linker_composite_defs_obligations)
    (p1 p2 p : program)
    (h : Ctypes.link_program certificate p1 p2 = some p) :
    ∃ ap tys,
      link (program_of_program p1) (program_of_program p2) = some ap ∧
      link_composite_defs p1.prog_types p2.prog_types = some tys ∧
      program_of_program p = ap ∧ p.prog_types = tys := by
  unfold Ctypes.link_program at h
  cases ha : link (program_of_program p1) (program_of_program p2) with
  | none => simp [ha] at h
  | some ap =>
      simp only [ha] at h
      cases ht : lift_option (link_composite_defs p1.prog_types p2.prog_types) with
      | inright hn => simp [ht] at h
      | inleft tys =>
          simp only [ht] at h
          cases h
          refine ⟨ap, tys.val, rfl, tys.property, ?_, rfl⟩
          cases ap
          rfl

private theorem sl_link_program_intro (certificate : Linker_composite_defs_obligations)
    (p1 p2 : program) (ap : sl_link_ast) (tys : List composite_definition)
    (ha : link (program_of_program p1) (program_of_program p2) = some ap)
    (ht : link_composite_defs p1.prog_types p2.prog_types = some tys) :
    ∃ p, Ctypes.link_program certificate p1 p2 = some p ∧
      program_of_program p = ap ∧ p.prog_types = tys := by
  unfold Ctypes.link_program
  rw [ha]
  cases he : lift_option (link_composite_defs p1.prog_types p2.prog_types) with
  | inright hn => rw [ht] at hn; contradiction
  | inleft typs =>
      refine ⟨_, rfl, ?_, ?_⟩
      · cases ap
        rfl
      · exact Option.some.inj (typs.property.symm.trans ht)

theorem TransfSimplLocalsLink (cfg : CompilerConfig)
    (clightLinkerCertificate : Linker_program_obligations) :
    TransfSimplLocalsLinkStatement cfg clightLinkerCertificate := by
  refine @TransfLink.mk program program
    (Ctypes.Linker_program function clightLinkerCertificate)
    (Ctypes.Linker_program function clightLinkerCertificate) (match_prog cfg) ?_
  intro p1 p2 tp1 tp2 p hl h1 h2
  change Ctypes.link_program clightLinkerCertificate.composite_defs p1 p2 = some p at hl
  obtain ⟨ap, tys, ha, ht, hp, htypes⟩ :=
    sl_link_program_inv clightLinkerCertificate.composite_defs p1 p2 p hl
  have ha' : link_prog (program_of_program p1) (program_of_program p2) = some ap := ha
  obtain ⟨tap, hta, hmatch⟩ := sl_link_ast_program cfg
    (program_of_program p1) (program_of_program p2)
    (program_of_program tp1) (program_of_program tp2) ap ha' h1.1 h2.1
  have htt : link_composite_defs tp1.prog_types tp2.prog_types = some tys := by
    rw [h1.2, h2.2]
    exact ht
  obtain ⟨tp, hlp, hap, htp⟩ := sl_link_program_intro
    clightLinkerCertificate.composite_defs tp1 tp2 tap tys hta htt
  refine ⟨tp, hlp, ?_, htp.trans htypes.symm⟩
  rw [hp, hap]
  exact hmatch

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Coqlib

theorem match_envs_extcall : match_envs_extcallStatement := by
  intro f cenv e le m lo hi te tle tlo thi tm f' m' hmatch hunch hincr hsep hhi hthi
  apply match_envs_invariant f cenv e le m lo hi te tle tlo thi f' m' hmatch
  · intro b chunk v hnone _ hload
    apply slp_load_unchanged_on (loc_unmapped f) m m' chunk b (.Z0 : Z) v hunch
    · intro i _
      exact hnone
    · exact hload
  · exact hincr
  · intro b hb
    by_cases hf : f b = none
    · cases hfp : f' b with
      | none => exact hf.symm
      | some pair =>
          rcases pair with ⟨b', delta⟩
          have hvb : Mem.valid_block m b :=
            Plt_Ple_trans b hi m.nextblock hb.2 hhi
          exact False.elim ((hsep b b' delta hf hfp).1 hvb)
    · cases hff : f b with
      | none => exact False.elim (hf hff)
      | some pair =>
          rcases pair with ⟨b', delta⟩
          exact hincr b b' delta hff
  · intro b b' delta hmap hb'
    by_cases hf : f b = none
    · have hvb' : Mem.valid_block tm b' :=
        Plt_Ple_trans b' thi tm.nextblock hb'.2 hthi
      exact False.elim ((hsep b b' delta hf hmap).2 hvb')
    · cases hff : f b with
      | none => exact False.elim (hf hff)
      | some pair =>
          rcases pair with ⟨b0, delta0⟩
          exact hincr b b0 delta0 hff

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Maps

theorem match_envs_set_temp : match_envs_set_tempStatement := by
  intro f cenv e le m lo hi te tle tlo thi id v tv x hme hinj hcheck
  unfold check_temp at hcheck
  by_cases hmem : VSet.mem id cenv = true
  · simp [hmem] at hcheck
  · simp [hmem] at hcheck
    rcases hme with ⟨hvars, htemps, hinj_env, hrange, htrange,
      hmapped, hflat, hlo, htlo⟩
    refine ⟨?_, ?_, hinj_env, hrange, htrange, hmapped, hflat, hlo, htlo⟩
    · intro id0
      cases hvars id0 with
      | match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload htlenv hv =>
          have hne : id0 ≠ id := by
            intro heq
            subst id0
            exact hmem hlift
          exact match_var_lifted b ty chunk v0 tv0 henv htenv hlift hmap hmode hload
            (by
              have hg : PTree.get id0 (PTree.set id tv tle) = PTree.get id0 tle :=
                PTree.gso (A := val) (i := id0) (j := id) tv tle hne
              exact hg.trans htlenv)
            hv
      | match_var_not_lifted b ty b' henv htenv hnlocal hmap =>
          exact match_var_not_lifted b ty b' henv htenv hnlocal hmap
      | match_var_not_local henv htenv hnlocal =>
          exact match_var_not_local henv htenv hnlocal
    · intro id0 v0 hget
      change PTree.get id0 (PTree.set id v le) = some v0 at hget
      by_cases heq : id0 = id
      · subst id0
        have hs : PTree.get id (PTree.set id v le) = some v := PTree.gss id v le
        have hv0 : v = v0 := Option.some.inj (hs.symm.trans hget)
        subst v0
        refine ⟨⟨tv, PTree.gss id tv tle, hinj⟩, ?_⟩
        intro hmem'
        exact (hmem hmem').elim
      · have hget' : PTree.get id0 le = some v0 := by
          have hg : PTree.get id0 (PTree.set id v le) = PTree.get id0 le :=
            PTree.gso (A := val) (i := id0) (j := id) v le heq
          exact hg.symm.trans hget
        rcases htemps id0 v0 hget' with ⟨⟨tv0, htle, hv⟩, hcenv⟩
        refine ⟨⟨tv0, ?_, hv⟩, hcenv⟩
        change PTree.get id0 (PTree.set id tv tle) = some tv0
        have hg : PTree.get id0 (PTree.set id tv tle) = PTree.get id0 tle :=
          PTree.gso (A := val) (i := id0) (j := id) tv tle heq
        exact hg.trans htle

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem match_envs_temps_exten : match_envs_temps_extenStatement := by
  intro f cenv e le m lo hi te tle tlo thi tle' hmatch hext
  rcases hmatch with ⟨hvars, htemps, hinj, hrange, htrange,
    hmapped, hflat, hincr, htincr⟩
  refine ⟨?_, ?_, hinj, hrange, htrange, hmapped, hflat, hincr, htincr⟩
  · intro id
    cases hvars id with
    | match_var_lifted b ty chunk v tv henv htenv hlift hmap hmode hload htle hv =>
        exact match_var_lifted b ty chunk v tv henv htenv hlift hmap hmode hload
          ((hext id).trans htle) hv
    | match_var_not_lifted b ty b' henv htenv hlift hmap =>
        exact match_var_not_lifted b ty b' henv htenv hlift hmap
    | match_var_not_local henv htenv hlift =>
        exact match_var_not_local henv htenv hlift
  · intro id v hget
    rcases htemps id v hget with ⟨⟨tv, htle, hv⟩, hlift⟩
    exact ⟨⟨tv, (hext id).trans htle, hv⟩, hlift⟩

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem add_local_variable_charact : add_local_variable_charactStatement := by
  exact add_local_variable_charact_aux

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof
open Lean Elab Tactic Meta
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Lib.Integers

private def slpPrivateName (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem slp_wordcore_val_repr (bits : Nat) (i : Int) :
    (WordCore.repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let e ← mkAppM
      (slpPrivateName "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[mkFVar bF.fvarId, mkFVar iF.fvarId]
    closeMainGoal Name.anonymous e

private theorem slp_wordcore_intval_eq_zOfNat_val {bits : Nat} (x : WordCore.Word bits) :
    x.intval = ZArith.BinInt.Z.of_nat x.val := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let e ← mkAppM
      (slpPrivateName "CompCert4Lean.Lib.Integers.WordCore.intval_eq_zOfNat_val")
      #[mkFVar xF.fvarId]
    closeMainGoal Name.anonymous e

private theorem slp_ptrofs_modulus :
    Ptrofs.modulus = ZArith.BinInt.Z.of_nat (2 ^ Ptrofs.wordsize) := by
  unfold Ptrofs.modulus
  run_tac
    let e ← mkAppM
      (slpPrivateName "CompCert4Lean.Lib.Integers.WordCore.twoPowerNat_eq_zOfNat_twoPow")
      #[mkConst ``CompCert4Lean.Lib.Integers.Ptrofs.wordsize]
    closeMainGoal Name.anonymous e

private theorem slp_ptrofs_unsigned_repr (z : Z)
    (hz : ZArith.BinInt.Z.le (.Z0) z ∧ ZArith.BinInt.Z.le z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have hznonneg : 0 ≤ intOfZ z := by
    have hz0 := hz.1
    change 0 ≤ intOfZ z at hz0
    exact hz0
  have hzlt : intOfZ z < ((2 ^ Ptrofs.wordsize : Nat) : Int) := by
    have hzmax := hz.2
    change intOfZ z ≤ intOfZ Ptrofs.max_unsigned at hzmax
    unfold Ptrofs.max_unsigned at hzmax
    rw [slp_ptrofs_modulus] at hzmax
    change intOfZ z ≤ Int.ofNat (2 ^ Ptrofs.wordsize) - 1 at hzmax
    have hzmax' : intOfZ z ≤ ((2 ^ Ptrofs.wordsize : Nat) : Int) - 1 := by
      simpa only [Int.ofNat_eq_natCast] using hzmax
    omega
  change (WordCore.repr Ptrofs.wordsize z).intval = z
  rw [slp_wordcore_intval_eq_zOfNat_val]
  have hval :
      (WordCore.repr Ptrofs.wordsize z).val =
        Int.toNat (intOfZ z % ((2 ^ Ptrofs.wordsize : Nat) : Int)) := by
    rw [← zOfInt_intOfZ z]
    simpa only [intOfZ_zOfInt] using
      slp_wordcore_val_repr Ptrofs.wordsize (intOfZ z)
  rw [hval, Int.emod_eq_of_lt hznonneg hzlt]
  change zOfInt (Int.ofNat (Int.toNat (intOfZ z))) = z
  calc
    _ = zOfInt (intOfZ z) := congrArg zOfInt (Int.toNat_of_nonneg hznonneg)
    _ = z := zOfInt_intOfZ z

private theorem slp_address_inject
    (f : Val.meminj) (m tm : mem) (loc : block) (ofs : Ptrofs.int)
    (loc' : block) (delta : Z) (p : CompCert4Lean.Common.Memtype.permission) :
    Mem.inject f m tm →
    Mem.perm m loc (Ptrofs.unsigned ofs) Cur p →
    f loc = some (loc', delta) →
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) =
      ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) delta := by
  intro hinj hperm hmap
  have hpmax : Mem.perm m loc (Ptrofs.unsigned ofs) Max Nonempty := by
    exact Mem.perm_implies m loc (Ptrofs.unsigned ofs) Max p Nonempty
      (Mem.perm_cur_max m loc (Ptrofs.unsigned ofs) p hperm)
      (perm_any_N p)
  have hrep := hinj.mi_representable loc loc' delta ofs hmap (Or.inl hpmax)
  have hdelta0 : 0 ≤ intOfZ delta := by
    change 0 ≤ intOfZ delta
    exact hrep.1
  have hsum0 : 0 ≤ intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) delta) := by
    change 0 ≤ intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) delta)
    exact hrep.2.1
  have hsummax : intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) delta) ≤
      intOfZ Ptrofs.max_unsigned := by
    simpa only [ZArith.BinInt.Z.le] using hrep.2.2
  have hofs0 : 0 ≤ intOfZ (Ptrofs.unsigned ofs) := by
    have h := ofs.intrange.1
    change (-1 : Int) < intOfZ (Ptrofs.unsigned ofs) at h
    omega
  have hdeltaMax : intOfZ delta ≤ intOfZ Ptrofs.max_unsigned := by
    have hadd : intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs) delta) =
        intOfZ (Ptrofs.unsigned ofs) + intOfZ delta := by
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega
  have hu_delta : Ptrofs.unsigned (Ptrofs.repr delta) = delta :=
    slp_ptrofs_unsigned_repr delta ⟨by
      change 0 ≤ intOfZ delta
      exact hdelta0, by
      exact hdeltaMax⟩
  have haddrepr : Ptrofs.add ofs (Ptrofs.repr delta) =
      Ptrofs.repr (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs)
        (Ptrofs.unsigned (Ptrofs.repr delta))) := by rfl
  rw [haddrepr]
  rw [hu_delta]
  apply slp_ptrofs_unsigned_repr
  exact ⟨hsum0, hsummax⟩

private theorem slp_loadv_inject
    (f : Val.meminj) (m tm : mem) (chunk : memory_chunk)
    (a1 a2 v1 : val) :
    Mem.inject f m tm →
    Mem.loadv chunk m a1 = some v1 →
    Val.inject f a1 a2 →
    ∃ v2, Mem.loadv chunk tm a2 = some v2 ∧ Val.inject f v1 v2 := by
  intro hinj hload haddr
  cases a1 with
  | Vptr loc ofs =>
      cases a2 with
      | Vptr loc' ofs' =>
          cases haddr with
          | inject_ptr _ _ _ _ delta hmap hofs =>
              have hacc := Mem.load_valid_access m chunk loc
                (Ptrofs.unsigned ofs) v1 (by simpa [Mem.loadv] using hload)
              have hp : Mem.perm m loc (Ptrofs.unsigned ofs) Cur Readable := by
                apply hacc.1 (Ptrofs.unsigned ofs)
                constructor
                · exact ZArith.BinInt.Z.le_refl _
                · have hs := CompCert4Lean.Common.Memdata.size_chunk_pos chunk
                  change intOfZ (Ptrofs.unsigned ofs) <
                    intOfZ (ZArith.BinInt.Z.add (Ptrofs.unsigned ofs)
                      (CompCert4Lean.Common.Memdata.size_chunk chunk))
                  have hs' : 0 < intOfZ (CompCert4Lean.Common.Memdata.size_chunk chunk) := by
                    change 0 < intOfZ (CompCert4Lean.Common.Memdata.size_chunk chunk) at hs
                    exact hs
                  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
                  omega
              have haddr' := slp_address_inject f m tm loc ofs loc' delta
                Readable hinj hp hmap
              obtain ⟨v2, hload2, hinj2⟩ :=
                Mem.load_inj f m tm chunk loc (Ptrofs.unsigned ofs)
                  loc' delta v1 hinj.mi_inj
                  (by simpa [Mem.loadv] using hload) hmap
              refine ⟨v2, ?_, hinj2⟩
              simpa [Mem.loadv, hofs, haddr'] using hload2
      | Vundef => cases haddr
      | Vint _ => cases haddr
      | Vlong _ => cases haddr
      | Vfloat _ => cases haddr
      | Vsingle _ => cases haddr
  | Vundef => cases haddr <;> simp [Mem.loadv] at hload
  | Vint _ => cases haddr <;> simp [Mem.loadv] at hload
  | Vlong _ => cases haddr <;> simp [Mem.loadv] at hload
  | Vfloat _ => cases haddr <;> simp [Mem.loadv] at hload
  | Vsingle _ => cases haddr <;> simp [Mem.loadv] at hload

theorem deref_loc_inject : deref_loc_injectStatement := by
  intro m tm f hmem ty loc ofs bf v loc' ofs' hderef hptr
  cases hderef with
  | deref_loc_value chunk v hmode hload =>
      obtain ⟨tv, hload', hinj⟩ := slp_loadv_inject f m tm chunk
        (.Vptr loc ofs) (.Vptr loc' ofs') v hmem hload hptr
      exact ⟨tv, deref_loc_value chunk tv hmode hload', hinj⟩
  | deref_loc_reference hmode =>
      exact ⟨.Vptr loc' ofs', deref_loc_reference hmode, hptr⟩
  | deref_loc_copy hmode =>
      exact ⟨.Vptr loc' ofs', deref_loc_copy hmode, hptr⟩
  | deref_loc_bitfield sz sg pos width v hload =>
      cases hload with
      | load_bitfield_intro sz sg1 attr sg pos width m addr c hpos hwidth
          hcarrier hsg hload =>
          obtain ⟨tv, hload', hinj⟩ := slp_loadv_inject f m tm
            (chunk_for_carrier sz) (.Vptr loc ofs) (.Vptr loc' ofs') (.Vint c)
            hmem hload hptr
          cases hinj
          exact ⟨.Vint (bitfield_extract sz sg pos width c),
            deref_loc_bitfield sz sg pos width _
              (load_bitfield_intro sz sg1 attr sg pos width tm
                (.Vptr loc' ofs') c hpos hwidth hcarrier hsg hload'),
            Val.inject_int f _⟩

end CompCert4Lean.Cfrontend.SimplLocalsproof


namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Driver.Compopts
open CompCert4Lean.Lib.Maps

theorem step_Sset_debug
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_Sset_debugStatement := by
  intro cfg xi tprog f id ty a k e le m v v' heval hcast
  by_cases hd : CompCert4Lean.Driver.Compopts.debug cfg = true
  · simp [CompCert4Lean.Cfrontend.SimplLocals.Sset_debug, hd]
    refine plus_left
      (s2 := .State f
        (.Sset id (CompCert4Lean.Cfrontend.SimplLocals.make_cast a ty))
        (.Kseq (CompCert4Lean.Cfrontend.SimplLocals.Sdebug_temp id ty) k)
        e le m) _ E0 ?_ ?_ rfl
    · exact CompCert4Lean.Cfrontend.Clight.step.step_seq f
        (.Sset id (CompCert4Lean.Cfrontend.SimplLocals.make_cast a ty))
        (CompCert4Lean.Cfrontend.SimplLocals.Sdebug_temp id ty) k e le m
    · apply star_left
      · apply CompCert4Lean.Cfrontend.Clight.step.step_set
        exact make_cast_correct tprog e le m a v ty v' heval hcast
      · apply star_left
        · exact CompCert4Lean.Cfrontend.Clight.step.step_skip_seq f
            (CompCert4Lean.Cfrontend.SimplLocals.Sdebug_temp id ty) k e
            (PTree.set id v' le) m
        · apply star_one
          exact step_Sdebug_temp
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            xi tprog f id ty k e (PTree.set id v' le) m v'
            (PTree.gss id v' le) (CompCert4Lean.Cfrontend.Cop.cast_val_is_casted
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              v (CompCert4Lean.Cfrontend.Clight.typeof a) ty v' m hcast)
        · rfl
      · rfl
  · simp [CompCert4Lean.Cfrontend.SimplLocals.Sset_debug, hd]
    apply plus_one
    apply CompCert4Lean.Cfrontend.Clight.step.step_set
    exact make_cast_correct tprog e le m a v ty v' heval hcast

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem simpl_seq_of_labeled_statement_proof : CompCert4Lean.Cfrontend.SimplLocalsproof.simpl_seq_of_labeled_statementStatement :=
  simpl_seq_of_labeled_statement

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

theorem match_envs_assign_lifted : match_envs_assign_liftedStatement := by
  intro sourceProgram mapping compilationEnvironment environment temporaries memory
    low high targetEnvironment targetTemporaries targetLow targetHigh assignedBlock
    assignedType value newMemory identifier targetValue matched environmentEntry
    casted valueInjection assignment lifted
  have variableFacts : ∃ chunk,
      PTree.get identifier targetEnvironment = none ∧ mapping assignedBlock = none ∧
      access_mode assignedType = .By_value chunk := by
    cases matched.me_vars identifier with
    | match_var_lifted sourceBlock sourceType chunk oldValue oldTarget
        sourceEntry targetEntry isLifted unmapped mode loaded targetTemp injected =>
        have sameEntry := Option.some.inj (sourceEntry.symm.trans environmentEntry)
        cases sameEntry
        exact ⟨chunk, targetEntry, unmapped, mode⟩
    | match_var_not_lifted sourceBlock sourceType targetBlock
        sourceEntry targetEntry notLifted mapped =>
        rw [lifted] at notLifted
        contradiction
    | match_var_not_local sourceEntry targetEntry notLifted =>
        rw [lifted] at notLifted
        contradiction
  rcases variableFacts with ⟨chunk, targetMissing, unmapped, mode⟩
  have stored : Mem.store chunk memory assignedBlock .Z0 value = some newMemory := by
    cases assignment with
    | assign_loc_value assignedValue assignedChunk resultMemory assignedMode stored =>
        have sameChunk : assignedChunk = chunk := by
          cases assignedMode.symm.trans mode
          rfl
        subst assignedChunk
        change Mem.store chunk memory assignedBlock .Z0 value = some newMemory at stored
        exact stored
    | assign_loc_copy sourceBlock sourceOffset bytes resultMemory
        assignedMode alignedSource alignedTarget separated loaded stored =>
        rw [mode] at assignedMode
        contradiction
  have loaded : Mem.load chunk newMemory assignedBlock .Z0 = some value := by
    simpa only [val_casted_load_result value assignedType chunk casted mode] using
      Mem.load_store_same chunk memory assignedBlock .Z0 value newMemory stored
  refine ⟨?_, ?_, matched.me_inj, matched.me_range, matched.me_trange,
    matched.me_mapped, matched.me_flat, matched.me_incr, matched.me_tincr⟩
  · intro queried
    by_cases sameIdentifier : queried = identifier
    · subst queried
      exact match_var_lifted assignedBlock assignedType chunk value targetValue
        environmentEntry targetMissing lifted unmapped mode loaded
        (PTree.gss identifier targetValue targetTemporaries) valueInjection
    · cases matched.me_vars queried with
      | match_var_lifted otherBlock otherType otherChunk oldValue oldTarget
          sourceEntry targetEntry isLifted notMapped otherMode oldLoad oldTemp oldInjection =>
          refine match_var_lifted otherBlock otherType otherChunk oldValue oldTarget
            sourceEntry targetEntry isLifted notMapped otherMode ?_ ?_ oldInjection
          · rw [Mem.load_store_other chunk memory assignedBlock .Z0 value newMemory
              stored otherChunk otherBlock .Z0
              (Or.inl (matched.me_inj queried otherBlock otherType identifier
                assignedBlock assignedType sourceEntry environmentEntry sameIdentifier))]
            exact oldLoad
          · exact (PTree.gso (A := val) (i := queried) (j := identifier)
              targetValue targetTemporaries sameIdentifier).trans oldTemp
      | match_var_not_lifted otherBlock otherType targetBlock
          sourceEntry targetEntry notLifted mapped =>
          exact match_var_not_lifted otherBlock otherType targetBlock
            sourceEntry targetEntry notLifted mapped
      | match_var_not_local sourceEntry targetEntry notLifted =>
          exact match_var_not_local sourceEntry targetEntry notLifted
  · intro queried sourceValue sourceTemp
    rcases matched.me_temps queried sourceValue sourceTemp with
      ⟨⟨oldTarget, oldTemp, oldInjection⟩, undefinedIfLifted⟩
    refine ⟨?_, undefinedIfLifted⟩
    by_cases sameIdentifier : queried = identifier
    · subst queried
      rw [undefinedIfLifted lifted]
      exact ⟨targetValue, PTree.gss identifier targetValue targetTemporaries,
        Val.inject.val_inject_undef _⟩
    · exact ⟨oldTarget,
        (PTree.gso (A := val) (i := queried) (j := identifier)
          targetValue targetTemporaries sameIdentifier).trans oldTemp,
        oldInjection⟩

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Integers

private theorem slp_assign_unmapped_load
    (composites : composite_env) (assignedType : type) (mapping : meminj)
    (memory newMemory : mem) (destination targetDestination : block)
    (offset targetOffset : ptrofs) (field : bitfield) (value : val)
    (assignment : assign_loc composites assignedType memory destination offset
      field value newMemory)
    (pointerInjection : Val.inject mapping (.Vptr destination offset)
      (.Vptr targetDestination targetOffset)) :
    ∀ queried chunk oldValue, mapping queried = none →
      Mem.load chunk memory queried .Z0 = some oldValue →
      Mem.load chunk newMemory queried .Z0 = some oldValue := by
  intro queried chunk oldValue unmapped loaded
  have distinct : queried ≠ destination := by
    intro sameBlock
    subst queried
    cases pointerInjection with
    | inject_ptr sourceBlock sourceOffset targetBlock translatedOffset delta mapped shifted =>
        rw [unmapped] at mapped
        contradiction
  cases assignment with
  | assign_loc_value assignedValue assignedChunk resultMemory mode stored =>
      exact (Mem.load_store_other assignedChunk memory destination (Ptrofs.unsigned offset)
        value newMemory stored chunk queried .Z0 (Or.inl distinct)).trans loaded
  | assign_loc_copy sourceBlock sourceOffset bytes resultMemory
      mode sourceAligned destinationAligned separated sourceLoaded stored =>
      exact (Mem.load_storebytes_other memory destination (Ptrofs.unsigned offset)
        bytes newMemory stored chunk queried .Z0 (Or.inl distinct)).trans loaded
  | assign_loc_bitfield size sign position width assignedValue resultMemory normalized stored =>
      cases stored with
      | store_bitfield_intro size originalSign attributes sign position width
          sourceMemory address carrier raw resultMemory
          positionRange widthRange carrierRange signCorrect carrierLoaded carrierStored =>
          exact (Mem.load_store_other (chunk_for_carrier size) memory destination
            (Ptrofs.unsigned offset)
            (.Vint (CompCert4Lean.Lib.Integers.Int.bitfield_insert
              (first_bit size position width) width carrier raw)) newMemory carrierStored
            chunk queried .Z0 (Or.inl distinct)).trans loaded

set_option maxHeartbeats 1600000 in
theorem assign_loc_inject : assign_loc_injectStatement := by
  intro configuration sourceProgram targetProgram programs
  dsimp only
  intro mapping assignedType memory destination offset field value newMemory
    targetMemory targetDestination targetOffset targetValue assignment
    pointerInjection valueInjection memoryInjection
  rw [comp_env_preserved configuration sourceProgram targetProgram programs]
  let composites := (globalenv sourceProgram).genv_cenv
  have preserved := slp_assign_unmapped_load composites assignedType mapping memory newMemory
    destination targetDestination offset targetOffset field value assignment pointerInjection
  cases assignment with
  | assign_loc_value assignedValue chunk resultMemory mode stored =>
      obtain ⟨targetNewMemory, targetStored, injected⟩ :=
        Mem.storev_mapped_inject mapping chunk memory (.Vptr destination offset)
          value newMemory targetMemory (.Vptr targetDestination targetOffset)
          targetValue memoryInjection stored pointerInjection valueInjection
      exact ⟨targetNewMemory, assign_loc_value targetValue chunk targetNewMemory
        mode targetStored, injected, preserved⟩
  | assign_loc_copy sourceBlock sourceOffset bytes resultMemory
      mode sourceAligned destinationAligned separated loaded stored =>
      cases pointerInjection with
      | inject_ptr sourceDestination destinationOffset translatedDestination
          translatedOffset destinationDelta destinationMapped destinationShift =>
        cases valueInjection with
        | inject_ptr sourceBlock sourceOffset targetSource targetSourceOffset
            sourceDelta sourceMapped sourceShift =>
          subst targetOffset targetSourceOffset
          let byteCount := sizeof composites assignedType
          have sizeNonnegative : ZArith.BinInt.Z.le .Z0 byteCount :=
            sizeof_pos composites assignedType
          by_cases sizeZero : byteCount = .Z0
          · have bytesEmpty : bytes = [] := by
              apply Option.some.inj
              exact loaded.symm.trans (Mem.loadbytes_empty memory sourceBlock
                (Ptrofs.unsigned sourceOffset) byteCount (by
                  rw [sizeZero]
                  exact ZArith.BinInt.Z.le_refl _))
            subst bytes
            obtain ⟨targetNewMemory, targetStored⟩ := Mem.range_perm_storebytes targetMemory
              targetDestination (Ptrofs.unsigned (Ptrofs.add offset (Ptrofs.repr destinationDelta)))
              [] (by
                intro position bounds
                change intOfZ _ ≤ intOfZ position ∧ intOfZ position < intOfZ _ at bounds
                simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at bounds
                change _ ∧ intOfZ position < intOfZ _ + 0 at bounds
                omega)
            refine ⟨targetNewMemory, ?_, ?_, preserved⟩
            · refine assign_loc_copy targetSource
                (Ptrofs.add sourceOffset (Ptrofs.repr sourceDelta)) [] targetNewMemory
                mode ?_ ?_ ?_ ?_ targetStored
              · intro positiveSize
                change intOfZ byteCount > 0 at positiveSize
                rw [sizeZero] at positiveSize
                contradiction
              · intro positiveSize
                change intOfZ byteCount > 0 at positiveSize
                rw [sizeZero] at positiveSize
                contradiction
              · right
                right
                change ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ byteCount) _ ∨
                  ZArith.BinInt.Z.le (ZArith.BinInt.Z.add _ byteCount) _
                simp only [sizeZero, ZArith.BinInt.Z.le, ZArith.BinInt.Z.add, intOfZ_zOfInt]
                change _ + 0 ≤ _ ∨ _ + 0 ≤ _
                omega
              · exact Mem.loadbytes_empty targetMemory targetSource _ byteCount
                  (by rw [sizeZero]; exact ZArith.BinInt.Z.le_refl _)
            · exact Mem.storebytes_empty_inject mapping memory destination _ newMemory
                targetMemory targetDestination _ targetNewMemory memoryInjection stored targetStored
          · have sizePositive : ZArith.BinInt.Z.lt .Z0 byteCount := by
              change 0 ≤ intOfZ byteCount at sizeNonnegative
              have nonzero : intOfZ byteCount ≠ 0 := by
                intro zero
                apply sizeZero
                apply intOfZ_injective
                exact zero
              change 0 < intOfZ byteCount
              omega
            have byteLength : ZArith.BinInt.Z.of_nat bytes.length = byteCount := by
              rw [Mem.loadbytes_length memory sourceBlock (Ptrofs.unsigned sourceOffset)
                byteCount bytes loaded]
              exact ZArith.Znat.Z2Nat.id byteCount sizeNonnegative
            have sourceRange : Mem.range_perm memory sourceBlock (Ptrofs.unsigned sourceOffset)
                (ZArith.BinInt.Z.add (Ptrofs.unsigned sourceOffset) byteCount) Cur Nonempty :=
              Mem.range_perm_implies _ _ _ _ _ Readable Nonempty
                (Mem.loadbytes_range_perm memory sourceBlock _ byteCount bytes loaded)
                (perm_any_N _)
            have destinationRange : Mem.range_perm memory destination (Ptrofs.unsigned offset)
                (ZArith.BinInt.Z.add (Ptrofs.unsigned offset) byteCount) Cur Nonempty := by
              rw [← byteLength]
              exact Mem.range_perm_implies _ _ _ _ _ Writable Nonempty
                (Mem.storebytes_range_perm memory destination _ bytes newMemory stored)
                (perm_any_N _)
            have sourcePermission : Mem.perm memory sourceBlock (Ptrofs.unsigned sourceOffset)
                Cur Nonempty := by
              apply sourceRange
              constructor
              · exact ZArith.BinInt.Z.le_refl _
              · change 0 < intOfZ byteCount at sizePositive
                change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ byteCount)
                simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
                omega
            have destinationPermission : Mem.perm memory destination (Ptrofs.unsigned offset)
                Cur Nonempty := by
              apply destinationRange
              constructor
              · exact ZArith.BinInt.Z.le_refl _
              · change 0 < intOfZ byteCount at sizePositive
                change intOfZ _ < intOfZ (ZArith.BinInt.Z.add _ byteCount)
                simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
                omega
            have sourceAddress := Mem.address_inject mapping memory targetMemory sourceBlock
              sourceOffset targetSource sourceDelta Nonempty memoryInjection sourcePermission sourceMapped
            have destinationAddress := Mem.address_inject mapping memory targetMemory destination
              offset targetDestination destinationDelta Nonempty memoryInjection destinationPermission
              destinationMapped
            obtain ⟨targetBytes, targetLoaded, bytesInjected⟩ :=
              Mem.loadbytes_inject mapping memory targetMemory sourceBlock
                (Ptrofs.unsigned sourceOffset) byteCount targetSource sourceDelta bytes
                memoryInjection loaded sourceMapped
            obtain ⟨targetNewMemory, targetStored, injected⟩ :=
              Mem.storebytes_mapped_inject mapping memory destination (Ptrofs.unsigned offset)
                bytes newMemory targetMemory targetDestination destinationDelta targetBytes
                memoryInjection stored destinationMapped bytesInjected
            refine ⟨targetNewMemory, ?_, injected, preserved⟩
            refine assign_loc_copy targetSource
              (Ptrofs.add sourceOffset (Ptrofs.repr sourceDelta)) targetBytes targetNewMemory
              mode ?_ ?_ ?_ ?_ ?_
            · intro positiveSize
              rw [sourceAddress]
              exact Mem.aligned_area_inject mapping memory targetMemory sourceBlock
                (Ptrofs.unsigned sourceOffset) (alignof_blockcopy composites assignedType)
                byteCount targetSource sourceDelta memoryInjection
                (alignof_blockcopy_1248 composites assignedType) sizePositive
                (sizeof_alignof_blockcopy_compat composites assignedType)
                sourceRange (sourceAligned positiveSize) sourceMapped
            · intro positiveSize
              rw [destinationAddress]
              exact Mem.aligned_area_inject mapping memory targetMemory destination
                (Ptrofs.unsigned offset) (alignof_blockcopy composites assignedType)
                byteCount targetDestination destinationDelta memoryInjection
                (alignof_blockcopy_1248 composites assignedType) sizePositive
                (sizeof_alignof_blockcopy_compat composites assignedType)
                destinationRange (destinationAligned positiveSize) destinationMapped
            · rw [sourceAddress, destinationAddress]
              exact Mem.disjoint_or_equal_inject mapping memory targetMemory sourceBlock
                targetSource sourceDelta destination targetDestination destinationDelta
                (Ptrofs.unsigned sourceOffset) (Ptrofs.unsigned offset) byteCount
                memoryInjection sourceMapped destinationMapped
                (Mem.range_perm_max _ _ _ _ Cur Nonempty sourceRange)
                (Mem.range_perm_max _ _ _ _ Cur Nonempty destinationRange) sizePositive separated
            · rw [sourceAddress]
              exact targetLoaded
            · rw [destinationAddress]
              exact targetStored
  | assign_loc_bitfield size sign position width assignedValue resultMemory normalized stored =>
      cases stored with
      | store_bitfield_intro size originalSign attributes sign position width
          sourceMemory address carrier raw resultMemory
          positionRange widthRange carrierRange signCorrect carrierLoaded carrierStored =>
          cases valueInjection
          obtain ⟨targetCarrier, targetLoaded, carrierInjection⟩ :=
            Mem.loadv_inject mapping memory targetMemory (chunk_for_carrier size)
              (.Vptr destination offset) (.Vptr targetDestination targetOffset)
              (.Vint carrier) memoryInjection carrierLoaded pointerInjection
          cases carrierInjection
          obtain ⟨targetNewMemory, targetStored, injected⟩ :=
            Mem.storev_mapped_inject mapping (chunk_for_carrier size) memory
              (.Vptr destination offset) _ newMemory targetMemory
              (.Vptr targetDestination targetOffset) _ memoryInjection carrierStored
              pointerInjection (Val.inject.inject_int _)
          refine ⟨targetNewMemory, ?_, injected, preserved⟩
          exact assign_loc_bitfield size sign position width (.Vint raw) targetNewMemory
            (.Vint (bitfield_normalize size sign width raw))
            (store_bitfield_intro size originalSign attributes sign position width
              targetMemory (.Vptr targetDestination targetOffset) carrier raw targetNewMemory
              positionRange widthRange carrierRange signCorrect targetLoaded targetStored)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem slp_lifted_rvalue
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (sourceGlobals targetGlobals : genv) (environment targetEnvironment : env)
    (temporaries targetTemporaries : temp_env) (memory targetMemory : mem)
    (mapping : meminj) (compilationEnvironment : compilenv)
    (low high targetLow targetHigh : block)
    (matched : match_envs mapping compilationEnvironment environment temporaries memory
      low high targetEnvironment targetTemporaries targetLow targetHigh)
    (identifier : ident) (variableType : type) (location : block) (offset : ptrofs)
    (field : bitfield) (value : val)
    (locationEvaluation : eval_lvalue sourceGlobals environment temporaries memory
      (.Evar identifier variableType) location offset field)
    (loadedValue : deref_loc variableType memory location offset field value)
    (lifted : VSet.mem identifier compilationEnvironment = true) :
    ∃ targetValue, eval_expr targetGlobals targetEnvironment targetTemporaries targetMemory
      (.Etempvar identifier variableType) targetValue ∧ Val.inject mapping value targetValue := by
  cases locationEvaluation with
  | eval_Evar_local identifier location variableType environmentEntry =>
      cases matched.me_vars identifier with
      | match_var_lifted sourceBlock sourceType chunk oldValue oldTarget
          sourceEntry targetEntry isLifted unmapped mode loaded targetTemp injected =>
          have sameEntry := Option.some.inj (sourceEntry.symm.trans environmentEntry)
          cases sameEntry
          cases loadedValue with
          | deref_loc_value loadedChunk loadedResult loadedMode dereferenced =>
              have sameChunk : loadedChunk = chunk := by
                cases loadedMode.symm.trans mode
                rfl
              subst loadedChunk
              change Mem.load chunk memory location .Z0 = some value at dereferenced
              have sameValue := Option.some.inj (loaded.symm.trans dereferenced)
              cases sameValue
              exact ⟨oldTarget, eval_Etempvar identifier variableType oldTarget targetTemp, injected⟩
          | deref_loc_reference referenceMode =>
              rw [mode] at referenceMode
              contradiction
          | deref_loc_copy copyMode =>
              rw [mode] at copyMode
              contradiction
      | match_var_not_lifted sourceBlock sourceType targetBlock
          sourceEntry targetEntry notLifted mapped =>
          rw [lifted] at notLifted
          contradiction
      | match_var_not_local sourceEntry targetEntry notLifted =>
          rw [lifted] at notLifted
          contradiction
  | eval_Evar_global identifier location variableType localMissing symbol =>
      cases matched.me_vars identifier <;> simp_all

private theorem slp_nonlifted_expression (compilationEnvironment : compilenv) (expression : expr) :
    (∀ identifier expressionType, expression = .Evar identifier expressionType →
      VSet.mem identifier compilationEnvironment = false) →
    (match expression with
      | .Evar identifier _ => VSet.mem identifier compilationEnvironment = false
      | _ => True) := by
  cases expression <;> intro notLifted <;> try trivial
  exact notLifted _ _ rfl

set_option maxHeartbeats 2400000 in
private theorem slp_eval_simpl_mutual
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (configuration : CompilerConfig) (sourceProgram targetProgram : program)
    (programs : match_prog configuration sourceProgram targetProgram)
    (environment targetEnvironment : env) (temporaries targetTemporaries : temp_env)
    (memory targetMemory : mem) (mapping : meminj) (compilationEnvironment : compilenv)
    (low high targetLow targetHigh : block)
    (matched : match_envs mapping compilationEnvironment environment temporaries memory
      low high targetEnvironment targetTemporaries targetLow targetHigh)
    (memoryInjection : Mem.inject mapping memory targetMemory)
    (globals : ∃ bound, match_globalenvs sourceProgram mapping bound) :
    (∀ expression value,
      eval_expr (globalenv sourceProgram) environment temporaries memory expression value →
      compat_cenv (addr_taken_expr expression) compilationEnvironment →
      ∃ targetValue,
        eval_expr (globalenv targetProgram) targetEnvironment targetTemporaries targetMemory
          (simpl_expr compilationEnvironment expression) targetValue ∧
        Val.inject mapping value targetValue) ∧
    (∀ expression location offset field,
      eval_lvalue (globalenv sourceProgram) environment temporaries memory expression location offset field →
      compat_cenv (addr_taken_expr expression) compilationEnvironment →
      (match expression with
        | .Evar identifier _ => VSet.mem identifier compilationEnvironment = false
        | _ => True) →
      ∃ targetLocation targetOffset,
        eval_lvalue (globalenv targetProgram) targetEnvironment targetTemporaries targetMemory
          (simpl_expr compilationEnvironment expression) targetLocation targetOffset field ∧
        Val.inject mapping (.Vptr location offset) (.Vptr targetLocation targetOffset)) := by
  classical
  apply eval_expr_lvalue_ind
  · intro numeral expressionType compatible
    exact ⟨_, eval_expr.const_int numeral expressionType, Val.inject.inject_int _⟩
  · intro numeral expressionType compatible
    exact ⟨_, eval_expr.const_float numeral expressionType, Val.inject.inject_float _⟩
  · intro numeral expressionType compatible
    exact ⟨_, eval_expr.const_single numeral expressionType, Val.inject.inject_single _⟩
  · intro numeral expressionType compatible
    exact ⟨_, eval_expr.const_long numeral expressionType, Val.inject.inject_long _⟩
  · intro identifier expressionType value entry compatible
    obtain ⟨targetValue, targetEntry, injected⟩ := (matched.me_temps identifier value entry).1
    exact ⟨targetValue, eval_Etempvar identifier expressionType targetValue targetEntry, injected⟩
  · intro operand expressionType location offset evaluated inductionHypothesis compatible
    have operandCompatible : compat_cenv (addr_taken_expr operand) compilationEnvironment := by
      cases operand <;> simp only [addr_taken_expr] at compatible ⊢ <;> try exact compatible
      exact compat_cenv_empty compilationEnvironment
    have notLifted := slp_nonlifted_expression compilationEnvironment operand (by
      intro identifier variableType sameExpression
      subst operand
      cases membership : VSet.mem identifier compilationEnvironment with
      | false => rfl
      | true =>
          exact False.elim (compatible identifier
            (VSet.singleton_2_proof identifier identifier rfl)
            (VSet.mem_2_proof compilationEnvironment identifier membership)))
    obtain ⟨targetLocation, targetOffset, targetEvaluated, injected⟩ :=
      inductionHypothesis operandCompatible notLifted
    exact ⟨_, eval_Eaddrof (simpl_expr compilationEnvironment operand) expressionType
      targetLocation targetOffset targetEvaluated, injected⟩
  · intro operation operand expressionType operandValue value evaluated
      inductionHypothesis computed compatible
    obtain ⟨targetOperand, targetEvaluated, operandInjection⟩ := inductionHypothesis compatible
    obtain ⟨targetValue, targetComputed, injected⟩ :=
      sem_unary_operation_inject mapping memory targetMemory operation operandValue
        (typeof operand) value targetOperand computed operandInjection memoryInjection
    refine ⟨targetValue, eval_expr.unary operation (simpl_expr compilationEnvironment operand)
      expressionType targetOperand targetValue targetEvaluated ?_, injected⟩
    rw [typeof_simpl_expr compilationEnvironment operand]
    exact targetComputed
  · intro operation first second expressionType firstValue secondValue value
      firstEvaluated firstHypothesis secondEvaluated secondHypothesis computed compatible
    obtain ⟨firstTarget, firstTargetEvaluated, firstInjection⟩ := firstHypothesis
      (compat_cenv_union_l _ _ _ compatible)
    obtain ⟨secondTarget, secondTargetEvaluated, secondInjection⟩ := secondHypothesis
      (compat_cenv_union_r _ _ _ compatible)
    obtain ⟨targetValue, targetComputed, injected⟩ :=
      sem_binary_operation_inject mapping memory targetMemory (globalenv sourceProgram).genv_cenv
        operation firstValue (typeof first) secondValue (typeof second) value firstTarget secondTarget
        computed firstInjection secondInjection memoryInjection
    refine ⟨targetValue, eval_expr.binary operation (simpl_expr compilationEnvironment first)
      (simpl_expr compilationEnvironment second) expressionType firstTarget secondTarget targetValue
      firstTargetEvaluated secondTargetEvaluated ?_, injected⟩
    rw [typeof_simpl_expr compilationEnvironment first, typeof_simpl_expr compilationEnvironment second,
      comp_env_preserved configuration sourceProgram targetProgram programs]
    exact targetComputed
  · intro operand expressionType operandValue value evaluated inductionHypothesis computed compatible
    obtain ⟨targetOperand, targetEvaluated, operandInjection⟩ := inductionHypothesis compatible
    obtain ⟨targetValue, targetComputed, injected⟩ :=
      sem_cast_inject mapping operandValue (typeof operand) expressionType memory value
        targetOperand targetMemory computed operandInjection memoryInjection
    refine ⟨targetValue, eval_expr.cast (simpl_expr compilationEnvironment operand) expressionType
      targetOperand targetValue targetEvaluated ?_, injected⟩
    rw [typeof_simpl_expr compilationEnvironment operand]
    exact targetComputed
  · intro measuredType expressionType compatible
    refine ⟨_, eval_expr.sizeof_type measuredType expressionType, ?_⟩
    rw [comp_env_preserved configuration sourceProgram targetProgram programs]
    exact Val.inject.inject_long _
  · intro measuredType expressionType compatible
    refine ⟨_, eval_expr.alignof_type measuredType expressionType, ?_⟩
    rw [comp_env_preserved configuration sourceProgram targetProgram programs]
    exact Val.inject.inject_long _
  · intro expression location offset field value evaluated inductionHypothesis loaded compatible
    by_cases liftedExpression : ∃ identifier expressionType,
        expression = .Evar identifier expressionType ∧
        VSet.mem identifier compilationEnvironment = true
    · obtain ⟨identifier, expressionType, sameExpression, lifted⟩ := liftedExpression
      subst expression
      simpa only [simpl_expr, lifted, if_true] using
        slp_lifted_rvalue (globalenv sourceProgram) (globalenv targetProgram)
          environment targetEnvironment temporaries targetTemporaries memory targetMemory
          mapping compilationEnvironment low high targetLow targetHigh matched identifier
          expressionType location offset field value evaluated loaded lifted
    · have notLifted := slp_nonlifted_expression compilationEnvironment expression (by
        intro identifier expressionType sameExpression
        cases membership : VSet.mem identifier compilationEnvironment with
        | false => rfl
        | true =>
            exact False.elim (liftedExpression ⟨identifier, expressionType, sameExpression, membership⟩))
      obtain ⟨targetLocation, targetOffset, targetEvaluated, addressInjection⟩ :=
        inductionHypothesis compatible notLifted
      obtain ⟨targetValue, targetLoaded, injected⟩ := deref_loc_inject memory targetMemory mapping
        memoryInjection (typeof expression) location offset field value targetLocation targetOffset
        loaded addressInjection
      refine ⟨targetValue, eval_Elvalue (simpl_expr compilationEnvironment expression)
        targetLocation targetOffset field targetValue targetEvaluated ?_, injected⟩
      rw [typeof_simpl_expr compilationEnvironment expression]
      exact targetLoaded
  · intro identifier location variableType sourceEntry compatible notLifted
    cases matched.me_vars identifier with
    | match_var_lifted sourceBlock sourceType chunk oldValue oldTarget
        sourceEntry' targetEntry lifted unmapped mode loaded targetTemp injected =>
        rw [notLifted] at lifted
        contradiction
    | match_var_not_lifted sourceBlock sourceType targetBlock sourceEntry' targetEntry
        notLifted' mapped =>
        have sameEntry := Option.some.inj (sourceEntry'.symm.trans sourceEntry)
        cases sameEntry
        refine ⟨targetBlock, Ptrofs.zero, ?_, ?_⟩
        · simpa only [simpl_expr, notLifted, Bool.false_eq_true, if_false] using
            eval_Evar_local identifier targetBlock variableType targetEntry
        · exact Val.inject.inject_ptr location Ptrofs.zero targetBlock Ptrofs.zero .Z0 mapped rfl
    | match_var_not_local sourceMissing targetMissing notLifted' =>
        rw [sourceMissing] at sourceEntry
        contradiction
  · intro identifier location variableType sourceMissing symbol compatible notLifted
    have targetMissing : PTree.get identifier targetEnvironment = none := by
      cases matched.me_vars identifier with
      | match_var_lifted sourceBlock sourceType chunk oldValue oldTarget
          sourceEntry targetEntry lifted unmapped mode loaded targetTemp injected =>
          rw [sourceMissing] at sourceEntry
          contradiction
      | match_var_not_lifted sourceBlock sourceType targetBlock sourceEntry targetEntry
          notLifted' mapped =>
          rw [sourceMissing] at sourceEntry
          contradiction
      | match_var_not_local sourceMissing' targetMissing notLifted' => exact targetMissing
    refine ⟨location, Ptrofs.zero, ?_, ?_⟩
    · simp only [simpl_expr, notLifted, Bool.false_eq_true, if_false]
      apply eval_Evar_global identifier location variableType targetMissing
      rw [symbols_preserved configuration sourceProgram targetProgram programs]
      exact symbol
    · obtain ⟨bound, globalMatch⟩ := globals
      cases globalMatch with
      | intro domain image symbols functions variables =>
          exact Val.inject.inject_ptr location Ptrofs.zero location Ptrofs.zero .Z0
            (domain location (symbols identifier location symbol)) rfl
  · intro operand expressionType location offset evaluated inductionHypothesis compatible notLifted
    obtain ⟨targetValue, targetEvaluated, injected⟩ := inductionHypothesis compatible
    cases injected with
    | inject_ptr sourceBlock sourceOffset targetLocation targetOffset delta mapped shifted =>
        exact ⟨targetLocation, targetOffset,
          eval_Ederef (simpl_expr compilationEnvironment operand) expressionType
            targetLocation targetOffset targetEvaluated,
          Val.inject.inject_ptr location offset targetLocation targetOffset delta mapped shifted⟩
  · intro operand identifier expressionType location offset structIdentifier composite
      attributes fieldOffset field evaluated inductionHypothesis operandType compositeEntry
      fieldEntry compatible notLifted
    obtain ⟨targetValue, targetEvaluated, injected⟩ := inductionHypothesis compatible
    cases injected with
    | inject_ptr sourceBlock sourceOffset targetLocation targetOffset delta mapped shifted =>
        refine ⟨targetLocation, Ptrofs.add targetOffset (Ptrofs.repr fieldOffset), ?_, ?_⟩
        · apply eval_Efield_struct (simpl_expr compilationEnvironment operand) identifier
            expressionType targetLocation targetOffset structIdentifier composite attributes fieldOffset field
            targetEvaluated
          · rw [typeof_simpl_expr compilationEnvironment operand]
            exact operandType
          · simpa only [comp_env_preserved configuration sourceProgram targetProgram programs] using compositeEntry
          · simpa only [comp_env_preserved configuration sourceProgram targetProgram programs] using fieldEntry
        · apply Val.inject.inject_ptr
          · exact mapped
          · rw [shifted, Ptrofs.add_assoc_proof_api, Ptrofs.add_assoc_proof_api]
            congr 1
            exact Ptrofs.add_commut_proof_api _ _
  · intro operand identifier expressionType location offset unionIdentifier composite
      attributes fieldOffset field evaluated inductionHypothesis operandType compositeEntry
      fieldEntry compatible notLifted
    obtain ⟨targetValue, targetEvaluated, injected⟩ := inductionHypothesis compatible
    cases injected with
    | inject_ptr sourceBlock sourceOffset targetLocation targetOffset delta mapped shifted =>
        refine ⟨targetLocation, Ptrofs.add targetOffset (Ptrofs.repr fieldOffset), ?_, ?_⟩
        · apply eval_Efield_union (simpl_expr compilationEnvironment operand) identifier
            expressionType targetLocation targetOffset unionIdentifier composite attributes fieldOffset field
            targetEvaluated
          · rw [typeof_simpl_expr compilationEnvironment operand]
            exact operandType
          · simpa only [comp_env_preserved configuration sourceProgram targetProgram programs] using compositeEntry
          · simpa only [comp_env_preserved configuration sourceProgram targetProgram programs] using fieldEntry
        · apply Val.inject.inject_ptr
          · exact mapped
          · rw [shifted, Ptrofs.add_assoc_proof_api, Ptrofs.add_assoc_proof_api]
            congr 1
            exact Ptrofs.add_commut_proof_api _ _

theorem eval_simpl_expr :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_simpl_exprStatement := by
  intro binary64Certificate binary32Certificate configuration sourceProgram targetProgram programs
  dsimp only
  intro environment targetEnvironment temporaries targetTemporaries memory targetMemory mapping
    compilationEnvironment low high targetLow targetHigh matched memoryInjection globals
  exact (slp_eval_simpl_mutual configuration sourceProgram targetProgram programs environment
    targetEnvironment temporaries targetTemporaries memory targetMemory mapping compilationEnvironment
    low high targetLow targetHigh matched memoryInjection globals).1

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem eval_simpl_lvalue :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_simpl_lvalueStatement := by
  intro binary64Certificate binary32Certificate configuration sourceProgram targetProgram programs
  dsimp only
  intro environment targetEnvironment temporaries targetTemporaries memory targetMemory mapping
    compilationEnvironment low high targetLow targetHigh matched memoryInjection globals
  exact (slp_eval_simpl_mutual configuration sourceProgram targetProgram programs environment
    targetEnvironment temporaries targetTemporaries memory targetMemory mapping compilationEnvironment
    low high targetLow targetHigh matched memoryInjection globals).2

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.SimplLocals

theorem eval_simpl_exprlist :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      eval_simpl_exprlistStatement := by
  intro binary64Certificate binary32Certificate configuration sourceProgram targetProgram programs
  dsimp only
  intro environment targetEnvironment temporaries targetTemporaries memory targetMemory mapping
    compilationEnvironment low high targetLow targetHigh matched memoryInjection globals
    expressions types values evaluated
  induction evaluated with
  | nil =>
      intro compatible
      exact ⟨val_casted_list.nil, [], eval_exprlist.nil, Val.inject_list.inject_list_nil⟩
  | cons expression rest argumentType argumentTypes operandValue value values
      operandEvaluated casted restEvaluated inductionHypothesis =>
      intro compatible
      obtain ⟨targetOperand, targetEvaluated, operandInjection⟩ :=
        eval_simpl_expr configuration sourceProgram targetProgram programs environment
          targetEnvironment temporaries targetTemporaries memory targetMemory mapping
          compilationEnvironment low high targetLow targetHigh matched memoryInjection globals
          expression operandValue operandEvaluated (compat_cenv_union_l _ _ _ compatible)
      obtain ⟨targetValue, targetCasted, injected⟩ :=
        sem_cast_inject mapping operandValue (typeof expression) argumentType memory value
          targetOperand targetMemory casted operandInjection memoryInjection
      obtain ⟨restCasted, targetRest, targetRestEvaluated, restInjected⟩ :=
        inductionHypothesis (compat_cenv_union_r _ _ _ compatible)
      refine ⟨val_casted_list.cons value values argumentType argumentTypes
        (cast_val_is_casted operandValue (typeof expression) argumentType value memory casted)
        restCasted, targetValue :: targetRest, ?_, ?_⟩
      · exact eval_exprlist.cons (simpl_expr compilationEnvironment expression)
          (simpl_exprlist compilationEnvironment rest) argumentType argumentTypes
          targetOperand targetValue targetRest targetEvaluated
          (by rw [typeof_simpl_expr compilationEnvironment expression]; exact targetCasted)
          targetRestEvaluated
      · exact Val.inject_list.inject_list_cons _ _ _ _ injected restInjected

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem slp_lifted_assignment_memory
    (sourceProgram : program) (mapping : meminj) (compilationEnvironment : compilenv)
    (environment : env) (temporaries : temp_env) (memory targetMemory newMemory : mem)
    (low high targetLow targetHigh : block) (targetEnvironment : env)
    (targetTemporaries : temp_env) (identifier : ident) (location : block)
    (variableType : type) (value : val)
    (matched : match_envs mapping compilationEnvironment environment temporaries memory
      low high targetEnvironment targetTemporaries targetLow targetHigh)
    (memoryInjection : Mem.inject mapping memory targetMemory)
    (environmentEntry : PTree.get identifier environment = some (location, variableType))
    (assignment : assign_loc (globalenv sourceProgram).genv_cenv variableType memory location
      Ptrofs.zero .Full value newMemory)
    (lifted : VSet.mem identifier compilationEnvironment = true) :
    Mem.inject mapping newMemory targetMemory := by
  cases matched.me_vars identifier with
  | match_var_lifted sourceBlock sourceType chunk oldValue oldTarget
      sourceEntry targetEntry isLifted unmapped mode loaded targetTemp injected =>
      have sameEntry := Option.some.inj (sourceEntry.symm.trans environmentEntry)
      cases sameEntry
      cases assignment with
      | assign_loc_value assignedValue assignedChunk resultMemory assignedMode stored =>
          exact Mem.store_unmapped_inject mapping assignedChunk memory location
            (Ptrofs.unsigned Ptrofs.zero) value newMemory targetMemory memoryInjection stored unmapped
      | assign_loc_copy sourceBlock sourceOffset bytes resultMemory
          assignedMode sourceAligned targetAligned separated sourceLoaded stored =>
          rw [mode] at assignedMode
          contradiction
  | match_var_not_lifted sourceBlock sourceType targetBlock
      sourceEntry targetEntry notLifted mapped =>
      rw [lifted] at notLifted
      contradiction
  | match_var_not_local sourceEntry targetEntry notLifted =>
      rw [lifted] at notLifted
      contradiction

set_option maxHeartbeats 2400000 in
theorem store_params_correct :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      store_params_correctStatement := by
  intro binary64Certificate binary32Certificate configuration externalCalls
    sourceProgram targetProgram programs
  dsimp only
  intro mapping targetFunction targetContinuation compilationEnvironment temporaries
    low high targetEnvironment targetLow targetHigh environment memory parameters arguments
    newMemory bound
  induction bound with
  | nil memory =>
      intro body targetMemory originalTemps initialTemps targetArguments
        unique casted injected matched memoryInjection tempsEqual sourceMissing
      cases injected
      refine ⟨initialTemps, targetMemory, star_refl _ _ _, rfl, memoryInjection, ?_, rfl⟩
      apply match_envs_temps_exten mapping compilationEnvironment environment temporaries
        memory low high targetEnvironment originalTemps targetLow targetHigh initialTemps matched
      intro identifier
      exact tempsEqual identifier (by intro impossible; cases impossible)
  | cons memory identifier variableType parameters value values location intermediateMemory finalMemory
      environmentEntry assignment restBound inductionHypothesis =>
      intro body targetMemory originalTemps initialTemps targetArguments
        unique casted injected matched memoryInjection tempsEqual sourceMissing
      cases unique with
      | cons head headMissing uniqueTail =>
        cases casted with
        | cons headPair tailPair valueCasted valuesCasted =>
          cases injected with
          | inject_list_cons value targetValue values targetValues valueInjection valuesInjection =>
            have identifierMissing : identifier ∉ var_names parameters := headMissing
            have sourceMissingTail : ∀ queried, queried ∈ var_names parameters →
                PTree.get queried temporaries = none := by
              intro queried membership
              apply sourceMissing
              simp only [var_names, List.map_cons, List.mem_cons]
              exact Or.inr membership
            have tempsEqualTail : ∀ queried, queried ∉ var_names parameters →
                PTree.get queried (PTree.set identifier targetValue initialTemps) =
                  PTree.get queried (PTree.set identifier targetValue originalTemps) := by
              intro queried absent
              by_cases sameIdentifier : queried = identifier
              · subst queried
                exact (PTree.gss identifier targetValue initialTemps).trans
                  (PTree.gss identifier targetValue originalTemps).symm
              · rw [PTree.gso targetValue initialTemps sameIdentifier,
                  PTree.gso targetValue originalTemps sameIdentifier]
                apply tempsEqual
                simp only [var_names, List.map_cons, List.mem_cons, not_or]
                exact ⟨sameIdentifier, absent⟩
            have targetCasted : val_casted targetValue variableType :=
              val_casted_inject mapping value targetValue variableType valueInjection valueCasted
            cases lifted : VSet.mem identifier compilationEnvironment with
            | true =>
              have nextMatched := match_envs_assign_lifted sourceProgram mapping compilationEnvironment
                environment temporaries memory low high targetEnvironment originalTemps targetLow targetHigh
                location variableType value intermediateMemory identifier targetValue matched environmentEntry
                valueCasted valueInjection assignment lifted
              have nextMemoryInjection := slp_lifted_assignment_memory sourceProgram mapping
                compilationEnvironment environment temporaries memory targetMemory intermediateMemory
                low high targetLow targetHigh targetEnvironment originalTemps identifier location variableType
                value matched memoryInjection environmentEntry assignment lifted
              obtain ⟨finalTemps, finalTargetMemory, executed, tempsBound, finalInjected,
                  finalMatched, nextBlock⟩ := inductionHypothesis body targetMemory
                (PTree.set identifier targetValue originalTemps)
                (PTree.set identifier targetValue initialTemps) targetValues
                uniqueTail valuesCasted valuesInjection nextMatched nextMemoryInjection
                tempsEqualTail sourceMissingTail
              refine ⟨finalTemps, finalTargetMemory, ?_, tempsBound, finalInjected, finalMatched, nextBlock⟩
              simp only [store_params, lifted, if_true]
              split
              · have finalEntry : PTree.get identifier finalTemps = some targetValue :=
                  (bind_parameter_temps_inv identifier parameters targetValues
                    (PTree.set identifier targetValue initialTemps) finalTemps tempsBound identifierMissing).trans
                    (PTree.gss identifier targetValue initialTemps)
                apply star_left
                · exact step.step_seq targetFunction _ _ targetContinuation targetEnvironment finalTemps targetMemory
                · apply star_left
                  · exact step.step_set targetFunction identifier _ _ targetEnvironment finalTemps targetMemory
                      targetValue (make_cast_correct targetProgram targetEnvironment finalTemps targetMemory
                        (.Etempvar identifier variableType) targetValue variableType targetValue
                        (eval_Etempvar identifier variableType targetValue finalEntry)
                        (cast_val_casted targetValue variableType targetMemory targetCasted))
                  · rw [PTree.gsident identifier finalTemps finalEntry]
                    apply star_left
                    · exact step.step_skip_seq targetFunction _ targetContinuation targetEnvironment finalTemps targetMemory
                    · exact executed
                    · rfl
                  · rfl
                · rfl
              · exact executed
            | false =>
              have targetVariable : ∃ targetLocation,
                  PTree.get identifier targetEnvironment = some (targetLocation, variableType) ∧
                  mapping location = some (targetLocation, .Z0) := by
                cases matched.me_vars identifier with
                | match_var_lifted sourceBlock sourceType chunk oldValue oldTarget
                    sourceEntry targetEntry isLifted unmapped mode loaded targetTemp injected =>
                    rw [lifted] at isLifted
                    contradiction
                | match_var_not_lifted sourceBlock sourceType targetBlock sourceEntry
                    targetEntry notLifted mapped =>
                    have sameEntry := Option.some.inj (sourceEntry.symm.trans environmentEntry)
                    cases sameEntry
                    exact ⟨targetBlock, targetEntry, mapped⟩
                | match_var_not_local sourceEntry targetEntry notLifted =>
                    rw [environmentEntry] at sourceEntry
                    contradiction
              obtain ⟨targetLocation, targetEntry, mapped⟩ := targetVariable
              have pointerInjection : Val.inject mapping (.Vptr location Ptrofs.zero)
                  (.Vptr targetLocation Ptrofs.zero) :=
                Val.inject.inject_ptr location Ptrofs.zero targetLocation Ptrofs.zero .Z0 mapped rfl
              obtain ⟨intermediateTargetMemory, targetAssignment, nextMemoryInjection, preserved⟩ :=
                assign_loc_inject configuration sourceProgram targetProgram programs mapping variableType
                  memory location Ptrofs.zero .Full value intermediateMemory targetMemory targetLocation
                  Ptrofs.zero targetValue assignment pointerInjection valueInjection memoryInjection
              have preservedMatch := match_envs_invariant mapping compilationEnvironment environment
                temporaries memory low high targetEnvironment originalTemps targetLow targetHigh
                mapping intermediateMemory matched
                (fun queried chunk oldValue unmapped _ loaded => preserved queried chunk oldValue unmapped loaded)
                (inject_incr_refl mapping) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
              have nextMatched := match_envs_change_temp mapping compilationEnvironment environment
                temporaries intermediateMemory low high targetEnvironment originalTemps targetLow targetHigh
                identifier targetValue preservedMatch
                (sourceMissing identifier (by simp [var_names])) lifted
              obtain ⟨finalTemps, finalTargetMemory, executed, tempsBound, finalInjected,
                  finalMatched, nextBlock⟩ := inductionHypothesis body intermediateTargetMemory
                (PTree.set identifier targetValue originalTemps)
                (PTree.set identifier targetValue initialTemps) targetValues
                uniqueTail valuesCasted valuesInjection nextMatched nextMemoryInjection
                tempsEqualTail sourceMissingTail
              refine ⟨finalTemps, finalTargetMemory, ?_, tempsBound, finalInjected, finalMatched, ?_⟩
              · have finalEntry : PTree.get identifier finalTemps = some targetValue :=
                  (bind_parameter_temps_inv identifier parameters targetValues
                    (PTree.set identifier targetValue initialTemps) finalTemps tempsBound identifierMissing).trans
                    (PTree.gss identifier targetValue initialTemps)
                simp only [store_params, lifted, Bool.false_eq_true, if_false]
                apply star_left
                · exact step.step_seq targetFunction _ _ targetContinuation targetEnvironment finalTemps targetMemory
                · apply star_left
                  · exact step.step_assign targetFunction (.Evar identifier variableType)
                      (.Etempvar identifier variableType) _ targetEnvironment finalTemps targetMemory
                      targetLocation Ptrofs.zero .Full targetValue targetValue intermediateTargetMemory
                      (eval_Evar_local identifier targetLocation variableType targetEntry)
                      (eval_Etempvar identifier variableType targetValue finalEntry)
                      (cast_val_casted targetValue variableType targetMemory targetCasted) targetAssignment
                  · apply star_left
                    · exact step.step_skip_seq targetFunction _ targetContinuation targetEnvironment finalTemps intermediateTargetMemory
                    · exact executed
                    · rfl
                  · rfl
                · rfl
              · exact nextBlock.trans (assign_loc_nextblock _ _ _ _ _ _ _ _ targetAssignment)

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private theorem slp_return_type configuration sourceFunction targetFunction
    (translated : transf_function configuration sourceFunction = .OK targetFunction) :
    targetFunction.fn_return = sourceFunction.fn_return := by
  unfold transf_function at translated
  split at translated <;> try contradiction
  dsimp only at translated
  split at translated <;> try contradiction
  cases translated
  rfl

private theorem slp_switch_inject mapping value targetValue expressionType number
    (selected : sem_switch_arg value expressionType = some number)
    (injected : Val.inject mapping value targetValue) :
    sem_switch_arg targetValue expressionType = some number := by
  unfold sem_switch_arg at selected ⊢
  cases classified : classify_switch expressionType <;> rw [classified] at selected
  all_goals cases injected <;> first | exact selected | contradiction

private theorem slp_regular_simulation
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (configuration : CompilerConfig) (externalCalls : ExternalCalls) (sourceProgram targetProgram : program)
    (programs : match_prog configuration sourceProgram targetProgram)
    (sourceFunction : function) (sourceStatement : statement) (continuation : cont) (environment : env)
    (temporaries : temp_env) (memory : mem) (targetFunction : function) (targetStatement : statement)
    (targetContinuation : cont) (targetEnvironment : env) (targetTemporaries : temp_env) (targetMemory : mem)
    (mapping : meminj) (low high targetLow targetHigh : block)
    (functionTranslated : transf_function configuration sourceFunction = .OK targetFunction)
    (translated : simpl_stmt configuration (cenv_for sourceFunction) sourceStatement = .OK targetStatement)
    (environments : match_envs mapping (cenv_for sourceFunction) environment temporaries memory
      low high targetEnvironment targetTemporaries targetLow targetHigh)
    (continuations : match_cont configuration sourceProgram mapping (cenv_for sourceFunction)
      continuation targetContinuation memory low targetLow)
    (memoryInjection : Mem.inject mapping memory targetMemory)
    (compatible : compat_cenv (addr_taken_stmt sourceStatement) (cenv_for sourceFunction))
    (sourceBound : Ple high memory.nextblock) (targetBound : Ple targetHigh targetMemory.nextblock)
    (trace : trace) (next : state)
    (sourceStep : step1 externalCalls (globalenv sourceProgram)
      (.State sourceFunction sourceStatement continuation environment temporaries memory) trace next) :
    ∃ targetNext,
      plus (step2 externalCalls) (globalenv targetProgram)
        (.State targetFunction targetStatement targetContinuation targetEnvironment targetTemporaries targetMemory)
        trace targetNext ∧ match_states configuration sourceProgram next targetNext := by
  have globals := match_cont_globalenv configuration sourceProgram mapping (cenv_for sourceFunction)
    continuation targetContinuation memory low targetLow continuations
  have evaluate := eval_simpl_expr configuration sourceProgram targetProgram programs environment
    targetEnvironment temporaries targetTemporaries memory targetMemory mapping (cenv_for sourceFunction)
    low high targetLow targetHigh environments memoryInjection globals
  have evaluateList := eval_simpl_exprlist configuration sourceProgram targetProgram programs environment
    targetEnvironment temporaries targetTemporaries memory targetMemory mapping (cenv_for sourceFunction)
    low high targetLow targetHigh environments memoryInjection globals
  cases sourceStep with
  | step_assign _ left right _ _ _ _ location offset field rightValue value nextMemory
      leftEvaluated rightEvaluated casted assigned =>
      obtain ⟨targetRight, rightTargetEvaluated, rightInjection⟩ := evaluate right rightValue rightEvaluated
        (compat_cenv_union_r _ _ _ compatible)
      obtain ⟨targetValue, targetCasted, valueInjection⟩ := sem_cast_inject mapping rightValue
        (typeof right) (typeof left) memory value targetRight targetMemory casted rightInjection memoryInjection
      have liftable := is_liftable_var_charact (cenv_for sourceFunction) left
      simp only [simpl_stmt] at translated
      cases lifted : is_liftable_var (cenv_for sourceFunction) left with
      | some identifier =>
          rw [lifted] at liftable translated
          obtain ⟨variableType, sameExpression, liftedVariable⟩ := liftable
          subst left
          cases translated
          cases leftEvaluated with
          | eval_Evar_local _ _ _ entry =>
              refine ⟨_, step_Sset_debug configuration externalCalls targetProgram _ _ _ _ _ _ _ _
                targetRight targetValue rightTargetEvaluated ?_, ?_⟩
              · rw [typeof_simpl_expr (cenv_for sourceFunction) right]
                exact targetCasted
              · apply match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
                  functionTranslated rfl
                · exact match_envs_assign_lifted sourceProgram mapping (cenv_for sourceFunction)
                    environment temporaries memory low high targetEnvironment targetTemporaries targetLow targetHigh
                    location variableType value nextMemory identifier targetValue environments entry
                    (cast_val_is_casted _ _ _ _ _ casted) valueInjection assigned liftedVariable
                · exact match_cont_assign_loc configuration sourceProgram mapping (cenv_for sourceFunction)
                    continuation targetContinuation memory low targetLow variableType location Ptrofs.zero .Full
                    value nextMemory continuations assigned (environments.me_range identifier location variableType entry).1
                · exact slp_lifted_assignment_memory sourceProgram mapping (cenv_for sourceFunction)
                    environment temporaries memory targetMemory nextMemory low high targetLow targetHigh
                    targetEnvironment targetTemporaries identifier location variableType value
                    environments memoryInjection entry assigned liftedVariable
                · exact compat_cenv_empty _
                · rw [assign_loc_nextblock _ _ _ _ _ _ _ _ assigned]
                  exact sourceBound
                · exact targetBound
          | eval_Evar_global _ _ _ missing symbol =>
              cases environments.me_vars identifier with
              | match_var_lifted _ _ _ _ _ entry _ _ _ _ _ _ _ => rw [missing] at entry; contradiction
              | match_var_not_lifted _ _ _ _ _ notLifted _ => rw [liftedVariable] at notLifted; contradiction
              | match_var_not_local _ _ notLifted => rw [liftedVariable] at notLifted; contradiction
      | none =>
          rw [lifted] at liftable translated
          cases translated
          obtain ⟨targetLocation, targetOffset, leftTargetEvaluated, addressInjection⟩ :=
            eval_simpl_lvalue configuration sourceProgram targetProgram programs environment targetEnvironment
              temporaries targetTemporaries memory targetMemory mapping (cenv_for sourceFunction)
              low high targetLow targetHigh environments memoryInjection globals left location offset field
              leftEvaluated (compat_cenv_union_l _ _ _ compatible) liftable
          obtain ⟨nextTargetMemory, targetAssigned, nextInjection, preserved⟩ := assign_loc_inject configuration
            sourceProgram targetProgram programs mapping (typeof left) memory location offset field value nextMemory
              targetMemory targetLocation targetOffset targetValue assigned addressInjection valueInjection memoryInjection
          refine ⟨_, plus_one _ _ _ _ _ _ _
            (step.step_assign _ _ _ _ _ _ _ targetLocation targetOffset field targetRight targetValue nextTargetMemory
              leftTargetEvaluated rightTargetEvaluated ?_ ?_), ?_⟩
          · rw [typeof_simpl_expr (cenv_for sourceFunction) right, typeof_simpl_expr (cenv_for sourceFunction) left]
            exact targetCasted
          · rw [typeof_simpl_expr (cenv_for sourceFunction) left]
            exact targetAssigned
          · apply match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated rfl
            · exact match_envs_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ environments
                (fun location chunk value unmapped range loaded => preserved location chunk value unmapped loaded)
                (inject_incr_refl _) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
            · exact match_cont_invariant configuration sourceProgram _ _ _ _ _ _ _ _ _ continuations
                (fun location chunk value unmapped bound loaded => preserved location chunk value unmapped loaded)
                (inject_incr_refl _) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
            · exact nextInjection
            · exact compat_cenv_empty _
            · rw [assign_loc_nextblock _ _ _ _ _ _ _ _ assigned]
              exact sourceBound
            · rw [assign_loc_nextblock _ _ _ _ _ _ _ _ targetAssigned]
              exact targetBound
  | step_set _ identifier expression _ _ _ _ value evaluated =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i checked temporaryChecked
      cases translated
      obtain ⟨targetValue, targetEvaluated, injected⟩ := evaluate expression value evaluated compatible
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_set _ _ _ _ _ _ _ targetValue targetEvaluated), ?_⟩
      exact match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
        functionTranslated rfl (match_envs_set_temp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ environments injected temporaryChecked)
        continuations memoryInjection (compat_cenv_empty _) sourceBound targetBound
  | step_call _ result expression arguments _ _ _ _ argumentTypes returnType callingConvention
      functionValue argumentValues callee classified evaluated argumentsEvaluated found calleeType =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i checked resultChecked
      cases translated
      obtain ⟨targetFunctionValue, targetEvaluated, functionInjection⟩ := evaluate expression functionValue
        evaluated (compat_cenv_union_l _ _ _ compatible)
      obtain ⟨castedArguments, targetArguments, targetArgumentsEvaluated, argumentsInjection⟩ :=
        evaluateList arguments argumentTypes argumentValues argumentsEvaluated (compat_cenv_union_r _ _ _ compatible)
      obtain ⟨targetCallee, targetFound, calleeTranslated⟩ := match_cont_find_funct configuration sourceProgram
        targetProgram programs mapping (cenv_for sourceFunction) continuation targetContinuation memory
        low targetLow functionValue callee targetFunctionValue continuations found functionInjection
      refine ⟨_, plus_one _ _ _ _ _ _ _
        (step.step_call _ _ _ _ _ _ _ _ argumentTypes returnType callingConvention targetFunctionValue
          targetArguments targetCallee ?_ targetEvaluated targetArgumentsEvaluated targetFound ?_), ?_⟩
      · rw [typeof_simpl_expr (cenv_for sourceFunction) expression]
        exact classified
      · rw [type_of_fundef_preserved configuration callee targetCallee calleeTranslated]
        exact calleeType
      · apply match_states.call _ _ _ _ _ _ _ _ mapping argumentTypes returnType callingConvention calleeTranslated
        · intro compilationEnvironment
          exact match_cont.match_Kcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            functionTranslated environments continuations resultChecked sourceBound targetBound
        · exact memoryInjection
        · exact argumentsInjection
        · exact calleeType
        · exact castedArguments
  | step_builtin _ result external argumentTypes arguments _ _ _ _ values events returned nextMemory evaluated called =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i checked resultChecked
      cases translated
      obtain ⟨castedArguments, targetArguments, targetEvaluated, argumentsInjection⟩ :=
        evaluateList arguments argumentTypes values evaluated compatible
      obtain ⟨nextMapping, targetReturned, nextTargetMemory, targetCalled, resultInjection,
        nextInjection, sourceUnchanged, targetUnchanged, increased, separated⟩ :=
        external_call_mem_inject externalCalls external _ _ (globalenv sourceProgram).genv_genv
          values memory trace returned nextMemory mapping targetMemory targetArguments
          (match_globalenvs_preserves_globals sourceProgram mapping globals) called memoryInjection argumentsInjection
      have targetCalled' := external_call_symbols_preserved_proof externalCalls external _ _ _ _ _ _ _
        (senv_preserved configuration sourceProgram targetProgram programs) targetCalled
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _
        targetEvaluated targetCalled'), ?_⟩
      apply match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ nextMapping low high targetLow targetHigh
        functionTranslated rfl
      · exact match_envs_set_opttemp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (match_envs_extcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ environments sourceUnchanged increased separated sourceBound targetBound)
          resultInjection resultChecked
      · exact match_cont_extcall configuration sourceProgram _ _ _ _ _ _ _ _ _ _ continuations
          sourceUnchanged increased separated (Ple_trans _ _ _ environments.me_incr sourceBound)
          (Ple_trans _ _ _ environments.me_tincr targetBound)
      · exact nextInjection
      · exact compat_cenv_empty _
      · exact Ple_trans _ _ _ sourceBound (external_call_nextblock _ _ _ _ _ _ _ _ called)
      · exact Ple_trans _ _ _ targetBound (external_call_nextblock _ _ _ _ _ _ _ _ targetCalled')
  | step_seq _ first second _ _ _ _ =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i targetFirst firstTranslated
      split at translated <;> try contradiction
      rename_i targetSecond secondTranslated
      cases translated
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_seq _ _ _ _ _ _ _), ?_⟩
      exact match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
        functionTranslated firstTranslated environments
        (match_cont.seq _ _ _ _ _ _ _ _ secondTranslated continuations (compat_cenv_union_r _ _ _ compatible))
        memoryInjection (compat_cenv_union_l _ _ _ compatible) sourceBound targetBound
  | step_skip_seq _ nextStatement remaining _ _ _ =>
      cases translated
      cases continuations with
      | seq _ _ _ targetNext targetRemaining _ _ _ nextTranslated remainingMatched nextCompatible =>
          exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_skip_seq _ _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated nextTranslated environments remainingMatched memoryInjection nextCompatible sourceBound targetBound⟩
  | step_continue_seq _ nextStatement remaining _ _ _ =>
      cases translated
      cases continuations with
      | seq _ _ _ targetNext targetRemaining _ _ _ nextTranslated remainingMatched nextCompatible =>
          exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_continue_seq _ _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated rfl environments remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound⟩
  | step_break_seq _ nextStatement remaining _ _ _ =>
      cases translated
      cases continuations with
      | seq _ _ _ targetNext targetRemaining _ _ _ nextTranslated remainingMatched nextCompatible =>
          exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_break_seq _ _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated rfl environments remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound⟩
  | step_ifthenelse _ condition first second _ _ _ _ value choice evaluated tested =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i targetFirst firstTranslated
      split at translated <;> try contradiction
      rename_i targetSecond secondTranslated
      cases translated
      obtain ⟨targetValue, targetEvaluated, injected⟩ := evaluate condition value evaluated
        (compat_cenv_union_l _ _ _ compatible)
      have statementsCompatible := compat_cenv_union_r _ _ _ compatible
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_ifthenelse _ _ _ _ _ _ _ _ targetValue choice
        targetEvaluated ?_), ?_⟩
      · rw [typeof_simpl_expr (cenv_for sourceFunction) condition]
        exact bool_val_inject mapping memory targetMemory value (typeof condition) choice targetValue
          tested injected memoryInjection
      · cases choice
        · exact match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
            functionTranslated secondTranslated environments continuations memoryInjection
            (compat_cenv_union_r _ _ _ statementsCompatible) sourceBound targetBound
        · exact match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
            functionTranslated firstTranslated environments continuations memoryInjection
            (compat_cenv_union_l _ _ _ statementsCompatible) sourceBound targetBound
  | step_loop _ body iteration _ _ _ _ =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i targetBody bodyTranslated
      split at translated <;> try contradiction
      rename_i targetIteration iterationTranslated
      cases translated
      exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_loop _ _ _ _ _ _ _),
        match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
          functionTranslated bodyTranslated environments
          (match_cont.loop1 _ _ _ _ _ _ _ _ _ _ bodyTranslated iterationTranslated continuations compatible)
          memoryInjection (compat_cenv_union_l _ _ _ compatible) sourceBound targetBound⟩
  | step_skip_or_continue_loop1 _ body iteration remaining _ _ _ current finished =>
      cases continuations with
      | loop1 _ _ _ _ targetBody targetIteration targetRemaining _ _ _ bodyTranslated iterationTranslated
          remainingMatched loopCompatible =>
          rcases finished with rfl | rfl
          all_goals
            cases translated
            exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_skip_or_continue_loop1 _ _ _ _ _ _ _ _ (by simp)),
              match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
                functionTranslated iterationTranslated environments
                (match_cont.loop2 _ _ _ _ _ _ _ _ _ _ bodyTranslated iterationTranslated remainingMatched loopCompatible)
                memoryInjection (compat_cenv_union_r _ _ _ loopCompatible) sourceBound targetBound⟩
  | step_break_loop1 _ body iteration remaining _ _ _ =>
      cases translated
      cases continuations with
      | loop1 _ _ _ _ targetBody targetIteration targetRemaining _ _ _ bodyTranslated iterationTranslated
          remainingMatched loopCompatible =>
          exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_break_loop1 _ _ _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated rfl environments remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound⟩
  | step_skip_loop2 _ body iteration remaining _ _ _ =>
      cases translated
      cases continuations with
      | loop2 _ _ _ _ targetBody targetIteration targetRemaining _ _ _ bodyTranslated iterationTranslated
          remainingMatched loopCompatible =>
          refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_skip_loop2 _ _ _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated ?_ environments remainingMatched memoryInjection loopCompatible sourceBound targetBound⟩
          simp only [simpl_stmt, bodyTranslated, iterationTranslated]
  | step_break_loop2 _ body iteration remaining _ _ _ =>
      cases translated
      cases continuations with
      | loop2 _ _ _ _ targetBody targetIteration targetRemaining _ _ _ bodyTranslated iterationTranslated
          remainingMatched loopCompatible =>
          exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_break_loop2 _ _ _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated rfl environments remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound⟩
  | step_return_0 _ _ _ _ _ nextMemory freed =>
      cases translated
      obtain ⟨nextTargetMemory, targetFreed, nextInjection⟩ := match_envs_free_blocks configuration sourceProgram
        targetProgram programs mapping (cenv_for sourceFunction) environment temporaries memory low high
        targetEnvironment targetTemporaries targetLow targetHigh nextMemory targetMemory environments memoryInjection freed
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_return_0 _ _ _ _ _ _ targetFreed),
        match_states.return_ _ _ _ _ _ _ mapping ?_ nextInjection (.val_inject_undef _)⟩
      intro compilationEnvironment
      exact match_cont_call_cont configuration sourceProgram _ _ _ _ _ _ _
        (match_cont_free_env configuration sourceProgram targetProgram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          environments continuations sourceBound targetBound freed targetFreed) compilationEnvironment
  | step_return_1 _ expression _ _ _ _ value castValue nextMemory evaluated casted freed =>
      cases translated
      obtain ⟨targetValue, targetEvaluated, injected⟩ := evaluate expression value evaluated compatible
      obtain ⟨targetCast, targetCasted, castInjection⟩ := sem_cast_inject mapping value (typeof expression)
        sourceFunction.fn_return memory castValue targetValue targetMemory casted injected memoryInjection
      obtain ⟨nextTargetMemory, targetFreed, nextInjection⟩ := match_envs_free_blocks configuration sourceProgram
        targetProgram programs mapping (cenv_for sourceFunction) environment temporaries memory low high
        targetEnvironment targetTemporaries targetLow targetHigh nextMemory targetMemory environments memoryInjection freed
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_return_1 _ _ _ _ _ _ targetValue targetCast nextTargetMemory
        targetEvaluated ?_ targetFreed), match_states.return_ _ _ _ _ _ _ mapping ?_ nextInjection castInjection⟩
      · rw [typeof_simpl_expr (cenv_for sourceFunction) expression, slp_return_type _ _ _ functionTranslated]
        exact targetCasted
      · intro compilationEnvironment
        exact match_cont_call_cont configuration sourceProgram _ _ _ _ _ _ _
          (match_cont_free_env configuration sourceProgram targetProgram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            environments continuations sourceBound targetBound freed targetFreed) compilationEnvironment
  | step_skip_call _ _ _ _ _ nextMemory isCall freed =>
      cases translated
      obtain ⟨nextTargetMemory, targetFreed, nextInjection⟩ := match_envs_free_blocks configuration sourceProgram
        targetProgram programs mapping (cenv_for sourceFunction) environment temporaries memory low high
        targetEnvironment targetTemporaries targetLow targetHigh nextMemory targetMemory environments memoryInjection freed
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_skip_call _ _ _ _ _ _
        (match_cont_is_call_cont configuration sourceProgram _ _ _ _ _ _ _ continuations isCall) targetFreed),
        match_states.return_ _ _ _ _ _ _ mapping ?_ nextInjection (.val_inject_undef _)⟩
      intro compilationEnvironment
      exact match_cont_change_cenv configuration sourceProgram _ _ _ _ _ _ _ compilationEnvironment
        (match_cont_free_env configuration sourceProgram targetProgram _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          environments continuations sourceBound targetBound freed targetFreed) isCall
  | step_switch _ selector labels _ _ _ _ value number evaluated selected =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i targetLabels labelsTranslated
      cases translated
      obtain ⟨targetValue, targetEvaluated, injected⟩ := evaluate selector value evaluated
        (compat_cenv_union_l _ _ _ compatible)
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_switch _ _ _ _ _ _ _ targetValue number targetEvaluated ?_), ?_⟩
      · rw [typeof_simpl_expr (cenv_for sourceFunction) selector]
        exact slp_switch_inject mapping value targetValue (typeof selector) number selected injected
      · apply match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
          functionTranslated
          (simpl_seq_of_labeled_statement_proof _ _ _ _ (simpl_select_switch _ _ _ _ _ labelsTranslated))
          environments (match_cont.switch _ _ _ _ _ _ continuations) memoryInjection ?_ sourceBound targetBound
        rw [addr_taken_seq_of_labeled_statement (select_switch number labels)]
        exact compat_cenv_select_switch _ _ _ (compat_cenv_union_r _ _ _ compatible)
  | step_skip_break_switch _ current remaining _ _ _ finished =>
      cases continuations with
      | switch _ _ targetRemaining _ _ _ remainingMatched =>
          rcases finished with rfl | rfl
          all_goals
            cases translated
            exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_skip_break_switch _ _ _ _ _ _ (by simp)),
              match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
                functionTranslated rfl environments remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound⟩
  | step_continue_switch _ remaining _ _ _ =>
      cases translated
      cases continuations with
      | switch _ _ targetRemaining _ _ _ remainingMatched =>
          exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_continue_switch _ _ _ _ _),
            match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
              functionTranslated rfl environments remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound⟩
  | step_label _ identifier body _ _ _ _ =>
      simp only [simpl_stmt] at translated
      split at translated <;> try contradiction
      rename_i targetBody bodyTranslated
      cases translated
      exact ⟨_, plus_one _ _ _ _ _ _ _ (step.step_label _ _ _ _ _ _ _),
        match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
          functionTranslated bodyTranslated environments continuations memoryInjection compatible sourceBound targetBound⟩
  | step_goto _ identifier _ _ _ _ nextStatement nextContinuation found =>
      cases translated
      have originalTranslation := functionTranslated
      unfold transf_function at functionTranslated
      split at functionTranslated <;> try contradiction
      dsimp only at functionTranslated
      split at functionTranslated <;> try contradiction
      rename_i targetBody bodyTranslated
      cases functionTranslated
      have labelMatched := simpl_find_label configuration sourceProgram mapping (cenv_for sourceFunction)
        memory low targetLow identifier sourceFunction.fn_body (call_cont continuation) targetBody
        (call_cont targetContinuation) bodyTranslated
        (match_cont_call_cont configuration sourceProgram _ _ _ _ _ _ _ continuations _)
        (compat_cenv_for sourceFunction)
      rw [found] at labelMatched
      obtain ⟨targetNextStatement, targetNextContinuation, targetFound, nextCompatible, nextTranslated, nextMatched⟩ := labelMatched
      refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_goto _ _ _ _ _ _ _ _ ?_),
        match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
          originalTranslation nextTranslated environments nextMatched memoryInjection nextCompatible sourceBound targetBound⟩
      change find_label identifier (add_debug_params configuration sourceFunction.fn_params
        (store_params (cenv_for sourceFunction) sourceFunction.fn_params
          (add_debug_vars configuration (remove_lifted (cenv_for sourceFunction)
            (sourceFunction.fn_params ++ sourceFunction.fn_vars)) targetBody)))
        (call_cont targetContinuation) = some (targetNextStatement, targetNextContinuation)
      rw [find_label_add_debug_params _ _ _ _ _, find_label_store_params _ _ _ _ _,
        find_label_add_debug_vars _ _ _ _ _]
      exact targetFound

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Cfrontend.SimplLocals
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Maps

theorem step_simulation
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    step_simulationStatement := by
  intro configuration externalCalls sourceProgram targetProgram programs
  dsimp only
  intro source trace next sourceStep target matched
  cases matched with
  | regular sourceFunction sourceStatement continuation environment temporaries memory targetFunction targetStatement
      targetContinuation targetEnvironment targetTemporaries targetMemory mapping low high targetLow targetHigh
      functionTranslated translated environments continuations memoryInjection compatible sourceBound targetBound =>
      exact slp_regular_simulation configuration externalCalls sourceProgram targetProgram programs sourceFunction
        sourceStatement continuation environment temporaries memory targetFunction targetStatement targetContinuation
        targetEnvironment targetTemporaries targetMemory mapping low high targetLow targetHigh functionTranslated translated
        environments continuations memoryInjection compatible sourceBound targetBound trace next sourceStep
  | call callee arguments continuation memory targetCallee targetArguments targetContinuation targetMemory mapping
      argumentTypes returnType callingConvention calleeTranslated continuations memoryInjection argumentsInjection
      calleeType castedArguments =>
      cases sourceStep with
      | step_internal_function sourceFunction _ _ _ environment temporaries nextMemory entered =>
          simp only [SimplLocals.transf_fundef] at calleeTranslated
          split at calleeTranslated <;> try contradiction
          rename_i targetFunction functionTranslated
          cases calleeTranslated
          cases entered with
          | intro allocatedMemory variablesDistinct allocated bound tempsCreated =>
              subst temporaries
              simp only [type_of_fundef, type_of_function] at calleeType
              cases calleeType
              have originalTranslation := functionTranslated
              unfold transf_function at functionTranslated
              split at functionTranslated <;> try contradiction
              rename_i disjointCheck
              have parametersDisjoint : list_disjoint (var_names sourceFunction.fn_params)
                  (var_names sourceFunction.fn_temps) :=
                proj_sumbool_true _ _ _ disjointCheck
              dsimp only at functionTranslated
              split at functionTranslated <;> try contradiction
              rename_i targetBody bodyTranslated
              cases functionTranslated
              let translatedFunction : function :=
                { fn_return := sourceFunction.fn_return
                  fn_callconv := sourceFunction.fn_callconv
                  fn_params := sourceFunction.fn_params
                  fn_vars := remove_lifted (cenv_for sourceFunction) (sourceFunction.fn_params ++ sourceFunction.fn_vars)
                  fn_temps := add_lifted (cenv_for sourceFunction) sourceFunction.fn_vars sourceFunction.fn_temps
                  fn_body := add_debug_params configuration sourceFunction.fn_params
                    (store_params (cenv_for sourceFunction) sourceFunction.fn_params
                      (add_debug_vars configuration (remove_lifted (cenv_for sourceFunction)
                        (sourceFunction.fn_params ++ sourceFunction.fn_vars)) targetBody)) }
              have allDistinct : list_norepet (var_names (sourceFunction.fn_params ++ sourceFunction.fn_vars)) := by
                rw [var_names_app]
                exact variablesDistinct
              obtain ⟨nextMapping, targetEnvironment, allocatedTargetMemory, targetAllocated, environments,
                allocatedInjection, increased, oldSource, oldTarget, targetEntries⟩ :=
                match_envs_alloc_variables configuration sourceProgram targetProgram programs
                  (cenv_for sourceFunction) memory (sourceFunction.fn_params ++ sourceFunction.fn_vars)
                  environment allocatedMemory sourceFunction.fn_temps mapping targetMemory allocated
                  allDistinct memoryInjection
                  (fun identifier variableType member lifted => cenv_for_gen_by_value _ _ _ _ member allDistinct
                    (VSet.mem_2_proof _ _ lifted))
                  (fun identifier lifted => cenv_for_gen_domain _ _ _ (VSet.mem_2_proof _ _ lifted))
              have parametersCasted := val_casted_list_params sourceFunction.fn_params arguments castedArguments
              have nextArgumentsInjection := val_inject_list_incr mapping nextMapping arguments targetArguments
                increased argumentsInjection
              obtain ⟨parametersDistinct, targetVariablesDistinct, targetTempsDisjoint⟩ :=
                vars_and_temps_properties (cenv_for sourceFunction) sourceFunction.fn_params sourceFunction.fn_vars
                  sourceFunction.fn_temps variablesDistinct parametersDisjoint
              obtain ⟨targetTemporaries, finalTargetMemory, parametersExecuted, parametersBound,
                finalInjection, finalEnvironments, sameNextBlock⟩ :=
                store_params_correct configuration externalCalls sourceProgram targetProgram programs
                  nextMapping translatedFunction targetContinuation (cenv_for sourceFunction) (create_undef_temps sourceFunction.fn_temps)
                  memory.nextblock allocatedMemory.nextblock targetEnvironment targetMemory.nextblock
                  allocatedTargetMemory.nextblock environment allocatedMemory sourceFunction.fn_params arguments
                  nextMemory bound
                  (add_debug_vars configuration (remove_lifted (cenv_for sourceFunction)
                    (sourceFunction.fn_params ++ sourceFunction.fn_vars)) targetBody)
                  allocatedTargetMemory
                  (create_undef_temps (add_lifted (cenv_for sourceFunction)
                    (sourceFunction.fn_params ++ sourceFunction.fn_vars) sourceFunction.fn_temps))
                  (create_undef_temps (add_lifted (cenv_for sourceFunction) sourceFunction.fn_vars sourceFunction.fn_temps))
                  targetArguments parametersDistinct parametersCasted nextArgumentsInjection environments allocatedInjection
                  (fun identifier notParameter => create_undef_temps_lifted identifier sourceFunction notParameter)
                  (by
                    intro identifier parameter
                    cases entry : PTree.get identifier (create_undef_temps sourceFunction.fn_temps) with
                    | none => rfl
                    | some value =>
                        have temporary := (create_undef_temps_inv sourceFunction.fn_temps identifier value entry).2
                        exact False.elim (parametersDisjoint identifier identifier parameter temporary rfl))
              refine ⟨.State translatedFunction targetBody targetContinuation targetEnvironment targetTemporaries finalTargetMemory,
                plus_left _ E0 (step.step_internal_function _ _ _ _ _ _ _
                (function_entry2.intro targetVariablesDistinct parametersDistinct targetTempsDisjoint
                  targetAllocated parametersBound)) ?_ rfl, ?_⟩
              · apply star_trans
                · exact step_add_debug_params configuration externalCalls targetProgram _ _ _ _ _ _
                    sourceFunction.fn_params targetArguments _ parametersDistinct
                    (forall2_val_casted_inject _ _ _ nextArgumentsInjection _ parametersCasted) parametersBound
                · apply star_trans
                  · exact parametersExecuted
                  · apply step_add_debug_vars
                    intro identifier variableType member
                    have member' := List.mem_filter.mp member
                    have notLifted : VSet.mem identifier (cenv_for sourceFunction) = false := by
                      simpa using member'.2
                    exact targetEntries identifier variableType member'.1 notLifted
                  · rfl
                · rfl
              · refine match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ nextMapping memory.nextblock
                  allocatedMemory.nextblock targetMemory.nextblock allocatedTargetMemory.nextblock
                  originalTranslation bodyTranslated finalEnvironments ?_ finalInjection
                  (compat_cenv_for sourceFunction) ?_ ?_
                · apply match_cont_invariant configuration sourceProgram nextMapping nextMemory mapping
                    (cenv_for sourceFunction) continuation targetContinuation memory memory.nextblock targetMemory.nextblock
                    (continuations (cenv_for sourceFunction)) ?_ increased oldSource oldTarget
                  intro location chunk value unmapped before loaded
                  rw [bind_parameters_load (globalenv sourceProgram) environment chunk location .Z0 (by
                    intro identifier allocatedLocation variableType entry sameLocation
                    obtain entryOld | range := alloc_variables_range (globalenv sourceProgram) identifier allocatedLocation
                      variableType empty_env memory (sourceFunction.fn_params ++ sourceFunction.fn_vars)
                      environment allocatedMemory allocated entry
                    · have absent : PTree.get identifier empty_env = none := PTree.gempty _ identifier
                      rw [absent] at entryOld
                      contradiction
                    · subst allocatedLocation
                      exact Plt_strict location (Plt_Ple_trans _ _ _ before range.1))
                    allocatedMemory sourceFunction.fn_params arguments nextMemory bound]
                  exact alloc_variables_load sourceProgram empty_env memory _ environment allocatedMemory allocated
                    chunk location .Z0 value loaded
                · rw [bind_parameters_nextblock _ _ _ _ _ _ bound]
                  exact Ple_refl _
                · rw [sameNextBlock]
                  exact Ple_refl _
      | step_external_function external sourceArgumentTypes sourceReturnType sourceConvention _ _ _ returned events nextMemory called =>
          cases calleeTranslated
          have globals := match_cont_globalenv configuration sourceProgram mapping VSet.empty continuation
            targetContinuation memory memory.nextblock targetMemory.nextblock (continuations VSet.empty)
          obtain ⟨nextMapping, targetReturned, nextTargetMemory, targetCalled, resultInjection, nextInjection,
            sourceUnchanged, targetUnchanged, increased, separated⟩ :=
            external_call_mem_inject externalCalls external _ _ (globalenv sourceProgram).genv_genv
              arguments memory trace returned nextMemory mapping targetMemory targetArguments
              (match_globalenvs_preserves_globals sourceProgram mapping globals) called memoryInjection argumentsInjection
          have targetCalled' := external_call_symbols_preserved_proof externalCalls external _ _ _ _ _ _ _
            (senv_preserved configuration sourceProgram targetProgram programs) targetCalled
          refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_external_function _ _ _ _ _ _ _ _ _ _ targetCalled'),
            match_states.return_ _ _ _ _ _ _ nextMapping ?_ nextInjection resultInjection⟩
          intro compilationEnvironment
          exact match_cont_incr_bounds configuration sourceProgram nextMapping compilationEnvironment
            continuation targetContinuation nextMemory memory.nextblock targetMemory.nextblock
            (match_cont_extcall configuration sourceProgram _ _ _ _ _ _ _ _ _ _
              (continuations compilationEnvironment) sourceUnchanged increased separated (Ple_refl _) (Ple_refl _))
            nextMemory.nextblock nextTargetMemory.nextblock
            (external_call_nextblock _ _ _ _ _ _ _ _ called) (external_call_nextblock _ _ _ _ _ _ _ _ targetCalled')
  | return_ returned continuation memory targetReturned targetContinuation targetMemory mapping
      continuations memoryInjection resultInjection =>
      cases sourceStep with
      | step_returnstate _ result sourceFunction environment temporaries remaining _ =>
          have callMatched := continuations (cenv_for sourceFunction)
          cases callMatched with
          | match_Kcall _ _ _ _ _ _ targetFunction targetEnvironment targetTemporaries targetRemaining _
              high targetHigh low targetLow _ _ checked functionTranslated environments remainingMatched
              resultChecked sourceBound targetBound =>
              refine ⟨_, plus_one _ _ _ _ _ _ _ (step.step_returnstate _ _ _ _ _ _ _), ?_⟩
              exact match_states.regular _ _ _ _ _ _ _ _ _ _ _ _ mapping low high targetLow targetHigh
                functionTranslated rfl
                (match_envs_set_opttemp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ environments resultInjection resultChecked)
                remainingMatched memoryInjection (compat_cenv_empty _) sourceBound targetBound

end CompCert4Lean.Cfrontend.SimplLocalsproof

namespace CompCert4Lean.Cfrontend.SimplLocalsproof

theorem transf_program_correct
    [BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    transf_program_correctStatement := by
  intro configuration externalCalls sourceProgram targetProgram programs
  exact CompCert4Lean.Common.Smallstep.forward_simulation_plus
    (Clight.semantics1 externalCalls sourceProgram) (Clight.semantics2 externalCalls targetProgram)
    (senv_preserved configuration sourceProgram targetProgram programs).2.1
    (match_states configuration sourceProgram)
    (initial_states_simulation configuration sourceProgram targetProgram programs)
    (final_states_simulation configuration sourceProgram)
    (step_simulation configuration externalCalls sourceProgram targetProgram programs)

end CompCert4Lean.Cfrontend.SimplLocalsproof
