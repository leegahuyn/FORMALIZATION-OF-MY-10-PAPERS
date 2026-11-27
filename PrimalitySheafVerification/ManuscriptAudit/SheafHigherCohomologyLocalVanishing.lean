import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundary

/-! Positive cohomology classes on an object are locally zero in the actual site topology. -/

namespace ManuscriptAudit.SheafHigherCohomologyLocalVanishing

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits ConcreteCategory Opposite
open SheafPresheafHOneBoundary

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{v}
private abbrev S := Sheaf J A

variable [HasSheafify J A] [HasExt.{w} (S J)]

def vanishingSieve (F : S J) (n : ℕ) {U : C} (x : F.H' n U) : Sieve U where
  arrows V f := (F.cohomologyPresheaf n).map f.op x = 0
  downward_closed := by
    intro V W f hf g
    change (F.cohomologyPresheaf n).map f.op x = 0 at hf
    change (F.cohomologyPresheaf n).map (g ≫ f).op x = 0
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf, map_zero]

private abbrev dimensionShift {F I : S J} (i : F ⟶ I) : ShortComplex (S J) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

private theorem dimensionShift_shortExact {F I : S J} (i : F ⟶ I) [Mono i] :
    (dimensionShift J i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

private theorem exists_boundary {F I : S J} (i : F ⟶ I) [Mono i] [Injective I]
    (U : C) (n : ℕ) (x : F.H' (n+1) U) :
    ∃ t : (cokernel i).H' n U, t.comp (dimensionShift_shortExact J i).extClass rfl = x := by
  have hx : x.comp (Ext.mk₀ i) (add_zero (n+1)) = 0 :=
    Ext.eq_zero_of_injective _
  have h := Ext.covariant_sequence_exact₁' ((freeYoneda J).obj U)
    (dimensionShift_shortExact J i) n (n+1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact (h x).1 hx

variable [enough : EnoughInjectives (S J)]
variable [composeForget : J.HasSheafCompose (forget A)] [wLocal : J.WEqualsLocallyBijective A]
variable [factorization : HasFunctorialSurjectiveInjectiveFactorization A]

include enough composeForget wLocal factorization in

/-- For every positive degree, the arrows killing a class constitute a covering sieve.
This formulation applies to the actual cohomology presheaf of an arbitrary sheaf. -/
theorem vanishingSieve_covering (n : ℕ) (F : S J) (U : C) (x : F.H' (n+1) U) :
    vanishingSieve J F (n+1) x ∈ J U := by
  induction n generalizing F U with
  | zero =>
    let i := Injective.ι F
    let Q := cokernel i
    let s := dimensionShift J i
    let hS := dimensionShift_shortExact J i
    obtain ⟨z, rfl⟩ := exists_boundary J i U 0 x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) Q).surjective z
    let q := sectionEquiv J Q U f
    have hf : sectionHom J Q U q = f := (sectionEquiv J Q U).symm_apply_apply f
    refine J.superset_covering ?_ (SheafH1Descent.cokernel_section_lift_sieve_mem i q)
    intro V g hg
    obtain ⟨a, ha⟩ := hg
    change (F.cohomologyPresheaf 1).map g.op ((Ext.mk₀ f).comp hS.extClass rfl) = 0
    rw [← hf]
    change (F.cohomologyPresheaf 1).map g.op (boundaryOfSection J s hS U q) = 0
    rw [boundaryOfSection_restrict]
    exact boundaryOfSection_zero_of_lift J s hS V _ a ha
  | succ n ih =>
    let i := Injective.ι F
    let Q := cokernel i
    let hS := dimensionShift_shortExact J i
    obtain ⟨z, rfl⟩ := exists_boundary J i U (n+1) x
    refine J.superset_covering ?_ (ih Q U z)
    intro V g hg
    change (Ext.mk₀ ((freeYoneda J).map g)).comp z (zero_add (n+1)) = 0 at hg
    change (Ext.mk₀ ((freeYoneda J).map g)).comp (z.comp hS.extClass rfl)
        (zero_add (n+1+1)) = 0
    rw [← Ext.comp_assoc_of_second_deg_zero, hg, Ext.zero_comp]

end
end ManuscriptAudit.SheafHigherCohomologyLocalVanishing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafHigherCohomologyLocalVanishing.vanishingSieve_covering
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
