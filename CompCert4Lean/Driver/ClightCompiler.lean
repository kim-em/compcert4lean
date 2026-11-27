import CompCert4Lean.Driver.Compiler

/-!
# Clight-to-Asm semantic preservation

The driver theorem `transf_c_program_correct` relates the Csem semantics of a
CompCert C program to its compiled Asm.  This module states the same guarantee
for the Clight program produced by `SimplLocals` (the `semantics2` view of
Clight): `transf_clight2_program` is the pipeline that starts at Cshmgen, and
`transf_c_program_clight_correct` gives a backward simulation from
`Clight.semantics2` of the `SimplLocals` output to the Asm produced by
`transf_c_program`.

The backward simulation comes from the composed forward simulation, the
receptiveness of `Clight.semantics2` (`Clight.semantics2_receptive`, CompCert's
`Clight.semantics_receptive`) and the determinacy of Asm.
-/

namespace CompCert4Lean.Cfrontend.Clight

open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

/-- Every Clight step emits at most one event, and a step can be replayed with
any trace that matches the one it emitted (CompCert's
`Clight.semantics_receptive`, for the `semantics2` parameter-passing
convention). -/
theorem semantics2_receptive
    [binary64_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls) (p : program) :
    receptive (semantics2 xi p) := by
  constructor
  · intro s t1 s1 t2 hstep hmatch
    change step2 xi (globalenv p) s t1 s1 at hstep
    change ∃ s2, step2 xi (globalenv p) s t2 s2
    have hstep0 := hstep
    cases hstep
    case step_builtin =>
        rename_i hargs hcall
        obtain ⟨vres2, m2, hcall2⟩ :=
          (external_call_spec xi _).ec_receptive _ _ _ _ _ _ _ hcall hmatch
        exact ⟨_, step_builtin _ _ _ _ _ _ _ _ _ _ _ _ _ hargs hcall2⟩
    case step_external_function =>
        rename_i hcall
        obtain ⟨vres2, m2, hcall2⟩ :=
          (external_call_spec xi _).ec_receptive _ _ _ _ _ _ _ hcall hmatch
        exact ⟨_, step_external_function _ _ _ _ _ _ _ _ _ _ hcall2⟩
    all_goals
      cases hmatch
      exact ⟨_, hstep0⟩
  · intro s t s' hstep
    change step2 xi (globalenv p) s t s' at hstep
    cases hstep
    case step_builtin =>
        rename_i hcall
        exact (external_call_spec xi _).ec_trace_length _ _ _ _ _ _ hcall
    case step_external_function =>
        rename_i hcall
        exact (external_call_spec xi _).ec_trace_length _ _ _ _ _ _ hcall
    all_goals simp [E0]

end CompCert4Lean.Cfrontend.Clight

namespace CompCert4Lean.Driver.Compiler

open CompCert4Lean.Common.Smallstep
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Cfrontend
open CompCert4Lean.Backend
open CompCert4Lean.X86

/-- The compiler pipeline from the output of `SimplLocals` (Clight with
temporaries as parameters) to Asm: Cshmgen, Cminorgen, then
`transf_cminor_program`. -/
def transf_clight2_program
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    [binary64_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Clight.program) : CompCert4Lean.Common.Errors.res Asm.program :=
  apply_partial _ _
    (apply_partial _ _ (Cshmgen.transl_program p) Cminorgen.transl_program)
    (transf_cminor_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle inlineCfg regallocOracle enumerationService)

/-- `transf_c_program` factors through `SimplExpr`, `SimplLocals` and
`transf_clight2_program`. -/
theorem transf_c_program_eq_clight2
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    [binary64_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (ctx : SimplExpr.FreshIdentContext)
    (p : Csyntax.program) (c1 c2 : Clight.program)
    (h1 : SimplExpr.transl_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ctx p = .OK c1)
    (h2 : SimplLocals.transf_program cfg c1 = .OK c2) :
    transf_c_program cfg selectionOracle inlineCfg regallocOracle enumerationService ctx p =
      transf_clight2_program cfg selectionOracle inlineCfg regallocOracle enumerationService
        c2 := by
  simp only [transf_c_program, transf_clight_program, transf_clight2_program, time, print,
    apply_total, apply_partial, h1, h2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The pipeline from Cshmgen onward is a forward simulation from
`Clight.semantics2` to Asm. -/
theorem transf_clight2_program_forward
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    [binary64_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (p : Clight.program) (tp : Asm.program)
    (compiled : transf_clight2_program cfg selectionOracle inlineCfg regallocOracle
      enumerationService p = .OK tp) :
    forward_simulation (Clight.semantics2 xi p) (Asm.semantics cfg xi tp) := by
  unfold transf_clight2_program transf_cminor_program transf_rtl_program at compiled
  simp only [time, print, apply_total, apply_partial] at compiled
  repeat first
    | contradiction
    | split at *
  all_goals
    simp_all only [CompCert4Lean.Common.Errors.res.OK.injEq]
    subst_vars
    refine compose_forward_simulations _ _ _
      (Cshmgenproof.transl_program_correct xi _ _
        (Cshmgenproof.transf_program_match _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (Cminorgenproof.transl_program_correct xi _ _
        (Cminorgenproof.transf_program_match _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (Selectionproof.transf_program_correct cfg selectionOracle xi _ _
        (Selectionproof.transf_program_match cfg selectionOracle _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (RTLgenproof.transf_program_correct xi _ _
        (RTLgenproof.transf_program_match _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics xi) _ _ _ _
        (total_if_match _ (fun _ => Compopts.optim_tailcalls cfg) _ _ _
          (Tailcallproof.transf_program_match cfg))
        (Tailcallproof.transf_program_correct cfg xi)) ?_
    refine compose_forward_simulations _ _ _
      (Inliningproof.transf_program_correct xi inlineCfg _ _
        (Inliningproof.transf_program_match inlineCfg _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (Renumberproof.transf_program_correct xi _ _
        (Renumberproof.transf_program_match _)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics xi) _ _ _ _
        (total_if_match _ (fun _ => Compopts.optim_constprop cfg) _ _ _
          (Constpropproof.transf_program_match cfg))
        (Constpropproof.transf_program_correct cfg xi)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics xi) _ _ _ _
        (total_if_match _ (fun _ => Compopts.optim_constprop cfg) _ _ _
          Renumberproof.transf_program_match)
        (Renumberproof.transf_program_correct xi)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics xi) _ _ _ _
        (partial_if_match _ (fun _ => Compopts.optim_CSE cfg) _ _ _ _
          (CSEproof.transf_program_match cfg) (by assumption))
        (CSEproof.transf_program_correct cfg xi)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (RTL.semantics xi) _ _ _ _
        (partial_if_match _ (fun _ => Compopts.optim_redundancy cfg) _ _ _ _
          (Deadcodeproof.transf_program_match cfg) (by assumption))
        (fun source target => Deadcodeproof.transf_program_correct cfg source target xi)) ?_
    refine compose_forward_simulations _ _ _
      (Unusedglobproof.transf_program_correct xi _ _
        (Unusedglobproof.transf_program_match _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (Allocproof.transf_program_correct cfg regallocOracle xi _ _
        (Allocproof.transf_program_match cfg regallocOracle _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (Tunnelingproof.transf_program_correct cfg xi _ _
        (Tunnelingproof.transf_program_match _)) ?_
    refine compose_forward_simulations _ _ _
      (Linearizeproof.transf_program_correct cfg xi enumerationService _ _
        (Linearizeproof.transf_program_match enumerationService _ _ (by assumption))) ?_
    refine compose_forward_simulations _ _ _
      (CleanupLabelsproof.transf_program_correct cfg xi _ _
        (CleanupLabelsproof.transf_program_match _)) ?_
    refine compose_forward_simulations _ _ _
      (match_if_simulation _ (Linear.semantics cfg xi) _ _ _ _
        (partial_if_match _ (fun _ => Compopts.debug cfg) _ _ _ _
          (Debugvarproof.transf_program_match cfg) (by assumption))
        (Debugvarproof.transf_program_correct cfg xi)) ?_
    refine compose_forward_simulations _ _ _
      (Stackingproof.transf_program_correct cfg xi Asmgenproof0.return_address_offset
        Asmgenproof.return_address_exists _ _
        (Bounds.function_bounds_bound_local_pos_proof cfg)
        (Bounds.function_bounds_bound_outgoing_pos_proof cfg)
        (Bounds.function_bounds_bound_stack_data_pos_proof cfg)
        (Bounds.function_bounds_used_callee_save_norepet_proof cfg)
        (Bounds.function_bounds_used_callee_save_prop_proof cfg)
        (Stackingproof.transf_program_match cfg _ _ (by assumption))) ?_
    exact Asmgenproof.transf_program_correct cfg xi _ _
      (Asmgenproof.transf_program_match _ _ compiled)

/-- The pipeline from Cshmgen onward is a backward simulation from
`Clight.semantics2` to Asm. -/
theorem transf_clight2_program_correct
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    [binary64_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (p : Clight.program) (tp : Asm.program)
    (compiled : transf_clight2_program cfg selectionOracle inlineCfg regallocOracle
      enumerationService p = .OK tp) :
    backward_simulation (Clight.semantics2 xi p) (Asm.semantics cfg xi tp) :=
  forward_to_backward_simulation _ _
    (transf_clight2_program_forward cfg selectionOracle inlineCfg regallocOracle
      enumerationService xi p tp compiled)
    (Clight.semantics2_receptive xi p)
    (Asm.semantics_determinate_proof cfg xi tp)

/-- Semantic preservation from the Clight program produced by `SimplLocals`
to the Asm program produced by `transf_c_program`. -/
theorem transf_c_program_clight_correct
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    [binary64_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_inverse_certificate :
      CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (ctx : SimplExpr.FreshIdentContext)
    (xi : CompCert4Lean.Common.ExternalCalls.ExternalCalls)
    (p : Csyntax.program) (c1 c2 : Clight.program) (tp : Asm.program)
    (compiled : transf_c_program cfg selectionOracle inlineCfg regallocOracle
      enumerationService ctx p = .OK tp)
    (h1 : SimplExpr.transl_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ctx p = .OK c1)
    (h2 : SimplLocals.transf_program cfg c1 = .OK c2) :
    backward_simulation (Clight.semantics2 xi c2) (Asm.semantics cfg xi tp) := by
  rw [transf_c_program_eq_clight2 cfg selectionOracle inlineCfg regallocOracle
    enumerationService ctx p c1 c2 h1 h2] at compiled
  exact transf_clight2_program_correct cfg selectionOracle inlineCfg regallocOracle
    enumerationService xi c2 tp compiled

end CompCert4Lean.Driver.Compiler
