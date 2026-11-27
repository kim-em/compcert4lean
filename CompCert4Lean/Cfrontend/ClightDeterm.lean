import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Common.Events

/-!
# Determinacy of Clight

`Clight.semantics2` is determinate in the sense of `Smallstep.determinate`:
expression evaluation, memory accesses, function entry and every non-external
transition are functional, and the only source of nondeterminism, the external
and builtin calls, is controlled by `ec_determ` and `ec_trace_length` of
`external_call_spec`.
-/

namespace CompCert4Lean.Cfrontend.Clight

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

theorem load_bitfield_determ {ty sz sg pos width m addr v1 v2}
    (h1 : load_bitfield ty sz sg pos width m addr v1)
    (h2 : load_bitfield ty sz sg pos width m addr v2) : v1 = v2 := by
  cases h1 with
  | load_bitfield_intro _ _ _ _ _ _ _ _ c1 _ _ _ _ hl1 =>
    cases h2 with
    | load_bitfield_intro _ _ _ _ _ _ _ _ c2 _ _ _ _ hl2 =>
      rw [hl1] at hl2
      cases hl2
      rfl

theorem store_bitfield_determ {ty sz sg pos width m addr v m1 v1 m2 v2}
    (h1 : store_bitfield ty sz sg pos width m addr v m1 v1)
    (h2 : store_bitfield ty sz sg pos width m addr v m2 v2) : m1 = m2 ∧ v1 = v2 := by
  cases h1 with
  | store_bitfield_intro _ _ _ _ _ _ _ _ c1 _ _ _ _ _ _ hl1 hs1 =>
    cases h2 with
    | store_bitfield_intro _ _ _ _ _ _ _ _ c2 _ _ _ _ _ _ hl2 hs2 =>
      rw [hl1] at hl2
      cases hl2
      rw [hs1] at hs2
      cases hs2
      exact ⟨rfl, rfl⟩

theorem deref_loc_determ {ty m b ofs bf v1 v2}
    (h1 : deref_loc ty m b ofs bf v1) (h2 : deref_loc ty m b ofs bf v2) : v1 = v2 := by
  cases h1 with
  | deref_loc_value c1 _ hm1 hl1 =>
    cases h2 with
    | deref_loc_value c2 _ hm2 hl2 =>
      rw [hm1] at hm2; cases hm2; rw [hl1] at hl2; cases hl2; rfl
    | deref_loc_reference hm2 => rw [hm1] at hm2; cases hm2
    | deref_loc_copy hm2 => rw [hm1] at hm2; cases hm2
  | deref_loc_reference hm1 =>
    cases h2 with
    | deref_loc_value c2 _ hm2 hl2 => rw [hm1] at hm2; cases hm2
    | deref_loc_reference hm2 => rfl
    | deref_loc_copy hm2 => rfl
  | deref_loc_copy hm1 =>
    cases h2 with
    | deref_loc_value c2 _ hm2 hl2 => rw [hm1] at hm2; cases hm2
    | deref_loc_reference hm2 => rfl
    | deref_loc_copy hm2 => rfl
  | deref_loc_bitfield _ _ _ _ _ hl1 =>
    cases h2 with
    | deref_loc_bitfield _ _ _ _ _ hl2 => exact load_bitfield_determ hl1 hl2

theorem assign_loc_determ {ce ty m b ofs bf v m1 m2}
    (h1 : assign_loc ce ty m b ofs bf v m1) (h2 : assign_loc ce ty m b ofs bf v m2) :
    m1 = m2 := by
  cases h1 with
  | assign_loc_value _ c1 _ hm1 hs1 =>
    cases h2 with
    | assign_loc_value _ c2 _ hm2 hs2 =>
      rw [hm1] at hm2; cases hm2; rw [hs1] at hs2; cases hs2; rfl
    | assign_loc_copy _ _ _ _ hm2 => rw [hm1] at hm2; cases hm2
  | assign_loc_copy _ _ _ _ hm1 _ _ _ hl1 hs1 =>
    cases h2 with
    | assign_loc_value _ c2 _ hm2 hs2 => rw [hm1] at hm2; cases hm2
    | assign_loc_copy _ _ _ _ _ _ _ _ hl2 hs2 =>
      rw [hl1] at hl2; cases hl2; rw [hs1] at hs2; cases hs2; rfl
  | assign_loc_bitfield _ _ _ _ _ _ _ hs1 =>
    cases h2 with
    | assign_loc_bitfield _ _ _ _ _ _ _ hs2 => exact (store_bitfield_determ hs1 hs2).1

variable [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
  [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
    (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]

theorem eval_expr_lvalue_determ (ge : genv) (e : env) (le : temp_env) (m : mem) :
    (∀ a v, eval_expr ge e le m a v → ∀ v', eval_expr ge e le m a v' → v = v') ∧
    (∀ a b ofs bf, eval_lvalue ge e le m a b ofs bf →
      ∀ b' ofs' bf', eval_lvalue ge e le m a b' ofs' bf' →
        b = b' ∧ ofs = ofs' ∧ bf = bf') := by
  apply eval_expr_lvalue_ind ge e le m
  · intro i ty v' h
    cases h with
    | const_int => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro f ty v' h
    cases h with
    | const_float => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro f ty v' h
    cases h with
    | const_single => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro i ty v' h
    cases h with
    | const_long => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro id ty v hfind v' h
    cases h with
    | eval_Etempvar _ _ _ hfind' => rw [hfind] at hfind'; cases hfind'; rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro a ty loc ofs _ ih v' h
    cases h with
    | eval_Eaddrof _ _ _ _ hl' =>
      obtain ⟨rfl, rfl, -⟩ := ih _ _ _ hl'
      rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro op a ty v1 v _ ih hop v' h
    cases h with
    | unary _ _ _ _ _ ha' hop' =>
      cases ih _ ha'
      rw [hop] at hop'; cases hop'; rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro op a1 a2 ty v1 v2 v _ ih1 _ ih2 hop v' h
    cases h with
    | binary _ _ _ _ _ _ _ ha1' ha2' hop' =>
      cases ih1 _ ha1'
      cases ih2 _ ha2'
      rw [hop] at hop'; cases hop'; rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro a ty v1 v _ ih hc v' h
    cases h with
    | cast _ _ _ _ ha' hc' =>
      cases ih _ ha'
      rw [hc] at hc'; cases hc'; rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro ty1 ty v' h
    cases h with
    | sizeof_type => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro ty1 ty v' h
    cases h with
    | alignof_type => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · intro a loc ofs bf v hlv ih hd v' h
    cases h with
    | eval_Elvalue _ _ _ _ _ hl' hd' =>
      obtain ⟨rfl, rfl, rfl⟩ := ih _ _ _ hl'
      exact deref_loc_determ hd hd'
    | _ => cases hlv
  · intro id loc ty hfind b' ofs' bf' h
    cases h with
    | eval_Evar_local _ _ _ hfind' =>
      rw [hfind] at hfind'; cases hfind'; exact ⟨rfl, rfl, rfl⟩
    | eval_Evar_global _ _ _ hlocal' _ => rw [hfind] at hlocal'; cases hlocal'
  · intro id loc ty hlocal hglobal b' ofs' bf' h
    cases h with
    | eval_Evar_local _ _ _ hfind' => rw [hlocal] at hfind'; cases hfind'
    | eval_Evar_global _ _ _ _ hglobal' =>
      rw [hglobal] at hglobal'; cases hglobal'; exact ⟨rfl, rfl, rfl⟩
  · intro a ty loc ofs _ ih b' ofs' bf' h
    cases h with
    | eval_Ederef _ _ _ _ ha' =>
      cases ih _ ha'; exact ⟨rfl, rfl, rfl⟩
  · intro a id ty loc ofs sid co att delta bf _ ih htype hco hoff b' ofs' bf' h
    cases h with
    | eval_Efield_struct _ _ _ _ _ _ _ _ _ _ ha' htype' hco' hoff' =>
      cases ih _ ha'
      rw [htype] at htype'; cases htype'
      rw [hco] at hco'; cases hco'
      rw [hoff] at hoff'; cases hoff'
      exact ⟨rfl, rfl, rfl⟩
    | eval_Efield_union _ _ _ _ _ _ _ _ _ _ _ htype' _ _ =>
      rw [htype] at htype'; cases htype'
  · intro a id ty loc ofs uid co att delta bf _ ih htype hco hoff b' ofs' bf' h
    cases h with
    | eval_Efield_struct _ _ _ _ _ _ _ _ _ _ _ htype' _ _ =>
      rw [htype] at htype'; cases htype'
    | eval_Efield_union _ _ _ _ _ _ _ _ _ _ ha' htype' hco' hoff' =>
      cases ih _ ha'
      rw [htype] at htype'; cases htype'
      rw [hco] at hco'; cases hco'
      rw [hoff] at hoff'; cases hoff'
      exact ⟨rfl, rfl, rfl⟩

theorem eval_expr_determ {ge e le m a v1 v2}
    (h1 : eval_expr ge e le m a v1) (h2 : eval_expr ge e le m a v2) : v1 = v2 :=
  (eval_expr_lvalue_determ ge e le m).1 _ _ h1 _ h2

theorem eval_lvalue_determ {ge e le m a b1 ofs1 bf1 b2 ofs2 bf2}
    (h1 : eval_lvalue ge e le m a b1 ofs1 bf1) (h2 : eval_lvalue ge e le m a b2 ofs2 bf2) :
    b1 = b2 ∧ ofs1 = ofs2 ∧ bf1 = bf2 :=
  (eval_expr_lvalue_determ ge e le m).2 _ _ _ _ h1 _ _ _ h2

theorem eval_exprlist_determ {ge e le m al tyl vl1 vl2}
    (h1 : eval_exprlist ge e le m al tyl vl1) (h2 : eval_exprlist ge e le m al tyl vl2) :
    vl1 = vl2 := by
  induction h1 generalizing vl2 with
  | nil => cases h2; rfl
  | cons _ _ _ _ _ _ _ ha hc _ ih =>
    cases h2 with
    | cons _ _ _ _ _ _ _ ha' hc' hrest' =>
      cases eval_expr_determ ha ha'
      rw [hc] at hc'; cases hc'
      rw [ih hrest']

omit binary64_certificate binary32_certificate in
theorem alloc_variables_determ {ge e m vars e1 m1 e2 m2}
    (h1 : alloc_variables ge e m vars e1 m1) (h2 : alloc_variables ge e m vars e2 m2) :
    e1 = e2 ∧ m1 = m2 := by
  induction h1 generalizing e2 m2 with
  | nil => cases h2; exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ _ _ _ _ ha _ ih =>
    cases h2 with
    | cons _ _ _ _ _ _ _ _ _ ha' hrest' =>
      rw [ha] at ha'; cases ha'
      exact ih hrest'

omit binary64_certificate binary32_certificate in
theorem function_entry2_determ {ge f vargs m e1 le1 m1 e2 le2 m2}
    (h1 : function_entry2 ge f vargs m e1 le1 m1)
    (h2 : function_entry2 ge f vargs m e2 le2 m2) :
    e1 = e2 ∧ le1 = le2 ∧ m1 = m2 := by
  cases h1 with
  | intro _ _ _ ha1 hb1 =>
    cases h2 with
    | intro _ _ _ ha2 hb2 =>
      obtain ⟨rfl, rfl⟩ := alloc_variables_determ ha1 ha2
      rw [hb1] at hb2; cases hb2
      exact ⟨rfl, rfl, rfl⟩

/-- Closes the pairs of `step` rules that either coincide outright or cannot
both apply to the same state. -/
local macro "step_trivial" : tactic =>
  `(tactic| first
    | exact ⟨.match_traces_E0, fun _ => rfl⟩
    | (exfalso; exact ‹is_call_cont _›)
    | (exfalso; rcases ‹_ ∨ _› with hs | hs <;> cases hs))

theorem step2_determ (xi : ExternalCalls) (ge : genv) {s t1 s1 t2 s2}
    (h1 : step2 xi ge s t1 s1) (h2 : step2 xi ge s t2 s2) :
    match_traces (Genv.to_senv ge.genv_genv) t1 t2 ∧ (t1 = t2 → s1 = s2) := by
  unfold step2 at h1 h2
  cases h1 with
  | step_assign _ _ _ _ _ _ _ _ _ _ _ _ _ hl hr hc ha =>
    cases h2 with
    | step_assign _ _ _ _ _ _ _ _ _ _ _ _ _ hl' hr' hc' ha' =>
      obtain ⟨rfl, rfl, rfl⟩ := eval_lvalue_determ hl hl'
      cases eval_expr_determ hr hr'
      rw [hc] at hc'; cases hc'
      cases assign_loc_determ ha ha'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_set _ _ _ _ _ _ _ _ h =>
    cases h2 with
    | step_set _ _ _ _ _ _ _ _ h' =>
      cases eval_expr_determ h h'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcl hf ha hfd _ =>
    cases h2 with
    | step_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcl' hf' ha' hfd' _ =>
      rw [hcl] at hcl'; cases hcl'
      cases eval_expr_determ hf hf'
      cases eval_exprlist_determ ha ha'
      rw [hfd] at hfd'; cases hfd'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ ha hc =>
    cases h2 with
    | step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ ha' hc' =>
      cases eval_exprlist_determ ha ha'
      obtain ⟨hm, heq⟩ := external_call_determ_proof xi _ _ _ _ _ _ _ _ _ _ hc hc'
      refine ⟨hm, fun ht => ?_⟩
      obtain ⟨rfl, rfl⟩ := heq ht
      rfl
    | _ => step_trivial
  | step_ifthenelse _ _ _ _ _ _ _ _ _ _ h hb =>
    cases h2 with
    | step_ifthenelse _ _ _ _ _ _ _ _ _ _ h' hb' =>
      cases eval_expr_determ h h'
      rw [hb] at hb'; cases hb'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_return_0 _ _ _ _ _ _ hf =>
    cases h2 with
    | step_return_0 _ _ _ _ _ _ hf' =>
      rw [hf] at hf'; cases hf'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_return_1 _ _ _ _ _ _ _ _ _ h hc hf =>
    cases h2 with
    | step_return_1 _ _ _ _ _ _ _ _ _ h' hc' hf' =>
      cases eval_expr_determ h h'
      rw [hc] at hc'; cases hc'
      rw [hf] at hf'; cases hf'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_skip_call _ _ _ _ _ _ _ hf =>
    cases h2 with
    | step_skip_call _ _ _ _ _ _ _ hf' =>
      rw [hf] at hf'; cases hf'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_switch _ _ _ _ _ _ _ _ _ h ha =>
    cases h2 with
    | step_switch _ _ _ _ _ _ _ _ _ h' ha' =>
      cases eval_expr_determ h h'
      rw [ha] at ha'; cases ha'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_goto _ _ _ _ _ _ _ _ hf =>
    cases h2 with
    | step_goto _ _ _ _ _ _ _ _ hf' =>
      rw [hf] at hf'; cases hf'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
    | _ => step_trivial
  | step_internal_function _ _ _ _ _ _ _ h =>
    cases h2 with
    | step_internal_function _ _ _ _ _ _ _ h' =>
      obtain ⟨rfl, rfl, rfl⟩ := function_entry2_determ h h'
      exact ⟨.match_traces_E0, fun _ => rfl⟩
  | step_external_function _ _ _ _ _ _ _ _ _ _ hc =>
    cases h2 with
    | step_external_function _ _ _ _ _ _ _ _ _ _ hc' =>
      obtain ⟨hm, heq⟩ := external_call_determ_proof xi _ _ _ _ _ _ _ _ _ _ hc hc'
      refine ⟨hm, fun ht => ?_⟩
      obtain ⟨rfl, rfl⟩ := heq ht
      rfl
  | _ => cases h2 <;> step_trivial

/-- Clight with temporaries as parameters is determinate: two steps from the
same state emit matching traces and, when the traces coincide, reach the same
state; every step emits at most one event; the initial state is unique; and a
final state has no step and a unique result. -/
theorem semantics2_determinate (xi : ExternalCalls) (p : program) :
    determinate (semantics2 xi p) where
  sd_determ := fun _ _ _ _ _ h1 h2 => step2_determ xi (globalenv p) h1 h2
  sd_traces := by
    intro s t s' hstep
    change step2 xi (globalenv p) s t s' at hstep
    cases hstep
    case step_builtin =>
      rename_i hcall
      exact (external_call_spec xi _).ec_trace_length _ _ _ _ _ _ hcall
    case step_external_function =>
      rename_i hcall
      exact (external_call_spec xi _).ec_trace_length _ _ _ _ _ _ hcall
    all_goals simp [E0]
  sd_initial_determ := by
    intro s1 s2 h1 h2
    cases h1 with
    | intro _ _ _ hm1 hs1 hf1 _ =>
      cases h2 with
      | intro _ _ _ hm2 hs2 hf2 _ =>
        rw [hm1] at hm2; cases hm2
        rw [hs1] at hs2; cases hs2
        rw [hf1] at hf2; cases hf2
        rfl
  sd_final_nostep := by
    intro s r hfinal t s' hstep
    cases hfinal
    cases hstep
  sd_final_determ := by
    intro s r1 r2 h1 h2
    cases h1
    cases h2
    rfl

end CompCert4Lean.Cfrontend.Clight
