import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.LaurentPowerKummer
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleIncreasingUnion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteAffineCover

/-! The infinite Laurent Kummer tower is a genuine pro-étale cover,
and its affine algebra carries all compatible coordinate roots. -/

namespace ManuscriptAudit.LaurentKummerTowerCover

open AlgebraicGeometry CategoryTheory
open LaurentKummerTowerAlgebra (Tower laurentMap)
open LaurentKummerTowerFiniteStages (stageMap link stageMap_comp_base stageMap_comp_link
  stageMap_injective laurentMap_injective exists_stage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev R := LaurentPolynomial K

local instance towerAlgebra : Algebra (R K) (Tower K ℓ) := (laurentMap K ℓ).toAlgebra

private abbrev stageAlgebra (n : ℕ) : Algebra (R K) (R K) :=
  (link K (ℓ ^ n)).toAlgebra

private def stageAlg (n : ℕ) :
    haveI : Algebra (R K) (R K) := stageAlgebra K ℓ n
    R K →ₐ[R K] Tower K ℓ := by
  letI := stageAlgebra K ℓ n
  refine { __ := stageMap K ℓ n, commutes' := ?_ }
  intro a
  exact RingHom.congr_fun (stageMap_comp_base K ℓ n) a

/-- The actual tower subalgebras over the original Laurent parameter. -/
def stages (n : ℕ) : Subalgebra (R K) (Tower K ℓ) :=
  letI := stageAlgebra K ℓ n
  (stageAlg K ℓ n).range

private def stageEquiv (n : ℕ) :
    haveI : Algebra (R K) (R K) := stageAlgebra K ℓ n
    R K ≃ₐ[R K] stages K ℓ n := by
  letI := stageAlgebra K ℓ n
  exact AlgEquiv.ofInjective (stageAlg K ℓ n)
    (stageMap_injective K ℓ (show ℓ.Prime from Fact.out).ne_zero n)

private theorem stages_mono : Monotone (stages K ℓ) :=
  monotone_nat_of_le_succ (fun n x hx ↦ by
    obtain ⟨a, rfl⟩ := hx
    refine ⟨link K ℓ a, ?_⟩
    exact RingHom.congr_fun (stageMap_comp_link K ℓ n) a)

private theorem stages_cover (u : Tower K ℓ) : ∃ n, u ∈ stages K ℓ n := by
  obtain ⟨n, v, hv⟩ := exists_stage K ℓ u
  exact ⟨n, ⟨v, hv⟩⟩

private theorem stage_finite_etale (n : ℕ) :
    IsFinite (Spec.map (CommRingCat.ofHom (link K (ℓ ^ n)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (link K (ℓ ^ n)))) := by
  have hp := pow_pos (show ℓ.Prime from Fact.out).pos n
  have hu : IsUnit ((ℓ ^ n : ℕ) : K) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr (NeZero.ne (ℓ : K))).pow n
  have h := LaurentPowerKummer.coverMap_finite_etale K (ℓ ^ n) hp hu
  exact ⟨h.1, h.2.1⟩

private theorem stages_etale (n : ℕ) : Algebra.Etale (R K) (stages K ℓ n) := by
  letI := stageAlgebra K ℓ n
  have he := (stage_finite_etale K ℓ n).2
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @Etale)] at he
  letI : Algebra.Etale (R K) (R K) := RingHom.etale_algebraMap.mp he
  exact Algebra.Etale.of_equiv (stageEquiv K ℓ n)

private theorem stages_integral (n : ℕ) : Algebra.IsIntegral (R K) (stages K ℓ n) := by
  letI := stageAlgebra K ℓ n
  have h := (IsFinite.SpecMap_iff (CommRingCat.ofHom (link K (ℓ ^ n)))).mp (stage_finite_etale K ℓ n).1
  letI : Module.Finite (R K) (R K) := RingHom.finite_algebraMap.mp h
  let e := stageEquiv K ℓ n
  letI : Module.Finite (R K) (stages K ℓ n) := Module.Finite.of_surjective e.toLinearMap e.surjective
  infer_instance

abbrev base := Spec (CommRingCat.of (R K))

/-- The actual map from the affine algebra with all reciprocal-power Laurent exponents. -/
abbrev coverMap : Spec (CommRingCat.of (Tower K ℓ)) ⟶ base K :=
  Spec.map (CommRingCat.ofHom (laurentMap K ℓ))

theorem cover_weaklyEtale : WeaklyEtale (coverMap K ℓ) :=
  WeaklyEtaleIncreasingUnion.weaklyEtale (stages K ℓ) (stages_mono K ℓ) (stages_cover K ℓ)
    (stages_etale K ℓ)

theorem cover_surjective : Surjective (coverMap K ℓ) :=
  WeaklyEtaleIncreasingUnion.surjective (stages K ℓ) (stages_cover K ℓ) (stages_integral K ℓ)
    (laurentMap_injective K ℓ (show ℓ.Prime from Fact.out).ne_zero)

local instance : WeaklyEtale (coverMap K ℓ) := cover_weaklyEtale K ℓ

abbrev coverObject : (base K).ProEt := Scheme.ProEt.mk (coverMap K ℓ)

abbrev terminalObject : (base K).ProEt := Scheme.ProEt.mk (𝟙 (base K))

def coverArrow : coverObject K ℓ ⟶ terminalObject K :=
  MorphismProperty.Over.homMk (coverMap K ℓ) (Category.comp_id _)

/-- The actual all-root chart is a singleton covering sieve in the native site. -/
theorem covering : Sieve.ofArrows (fun _ : Unit ↦ coverObject K ℓ)
    (fun _ : Unit ↦ coverArrow K ℓ) ∈ Scheme.ProEt.topology (base K) (terminalObject K) := by
  letI : IsAffine (terminalObject K).left := inferInstanceAs (IsAffine (base K))
  letI : Surjective (coverMap K ℓ) := cover_surjective K ℓ
  apply ProetaleFiniteAffineCover.covering
  · intro i
    exact inferInstanceAs (IsAffine (Spec (CommRingCat.of (Tower K ℓ))))
  · intro x
    obtain ⟨y, hy⟩ := (coverMap K ℓ).surj x
    exact ⟨(), y, hy⟩

end
end ManuscriptAudit.LaurentKummerTowerCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentKummerTowerCover.cover_weaklyEtale,
      ``ManuscriptAudit.LaurentKummerTowerCover.cover_surjective,
      ``ManuscriptAudit.LaurentKummerTowerCover.covering] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
