import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import PrimalitySheafVerification.ManuscriptAudit.RatFuncNormSurjectivity

/-!
# Even cohomology of finite cyclic unit representations over K(t)

The native periodic resolution identifies the positive even groups
with invariant units modulo norms. The invariant units are defined
over the base field by the finite Galois correspondence, and Tsen's
norm surjectivity makes each of these groups zero.
-/

namespace ManuscriptAudit.RatFuncTsen

open CategoryTheory Rep Rep.FiniteCyclicGroup

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- All positive even group cohomology groups of the unit
representation of a finite cyclic extension with surjective norm vanish. -/
theorem cyclic_units_even_subsingleton_of_norm (F E : Type) [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (hNorm : Function.Surjective (fun x : E ↦ Algebra.norm F x))
    (g : E ≃ₐ[F] E) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) [NeZero i] (hi : Even i) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F E) i) := by
  letI : CommGroup (E ≃ₐ[F] E) := IsCyclic.commGroup
  let A := Rep.ofAlgebraAutOnUnits F E
  let π := groupCohomologyπEven A g hg i hi
  have hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective π).mp inferInstance
  have hzero (y : groupCohomology A i) : y = 0 := by
    obtain ⟨x, rfl⟩ := hπ y
    apply (groupCohomologyπEven_eq_zero_iff A g hg i hi x).2
    have hd : A.ρ g x.val - x.val = 0 := x.property
    have hGen : A.ρ g x.val = x.val := sub_eq_zero.mp hd
    have hAll : ∀ k : E ≃ₐ[F] E, A.ρ k x.val = x.val :=
      (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x.val).2 hGen
    let ux : Eˣ := (Rep.toAdditive x.val).toMul
    have hFix (k : E ≃ₐ[F] E) : k (ux : E) = (ux : E) :=
      congrArg (fun q : A => ((Rep.toAdditive q).toMul : Eˣ).val) (hAll k)
    have hBase : (ux : E) ∈ (⊥ : IntermediateField F E) :=
      (IsGalois.mem_bot_iff_fixed (ux : E)).2 hFix
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hBase
    obtain ⟨v, hv⟩ := hNorm a
    have hvn : v ≠ 0 := by
      rintro rfl
      change Algebra.norm F (0 : E) = a at hv
      rw [Algebra.norm_zero] at hv
      exact ux.ne_zero (by rw [← ha, ← hv, map_zero])
    let u := Units.mk0 v hvn
    refine ⟨Rep.toAdditive.symm (Additive.ofMul u), ?_⟩
    change A.norm.hom (Rep.toAdditive.symm (Additive.ofMul u)) = x.val
    apply Rep.toAdditive.injective
    apply Additive.toMul.injective
    apply Units.ext
    exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq u).trans
      ((congrArg (algebraMap F E) hv).trans ha)
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- All positive even group cohomology groups vanish for the actual
unit representation of a finite cyclic extension of K(t). -/
theorem cyclic_units_even_subsingleton (K E : Type) [Field K] [IsAlgClosed K] [Field E]
    [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E] [IsGalois (RatFunc K) E]
    [IsCyclic (E ≃ₐ[RatFunc K] E)] (g : E ≃ₐ[RatFunc K] E)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) [NeZero i] (hi : Even i) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits (RatFunc K) E) i) :=
  cyclic_units_even_subsingleton_of_norm (RatFunc K) E (norm_surjective K E) g hg i hi

end

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.RatFuncTsen.cyclic_units_even_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
