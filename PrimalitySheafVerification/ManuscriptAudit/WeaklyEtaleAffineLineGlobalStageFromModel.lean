import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.TorsionFree
import PrimalitySheafVerification.ManuscriptAudit.AffineOpenStageSections
import PrimalitySheafVerification.ManuscriptAudit.DedekindFiniteProductAffineOpen
import PrimalitySheafVerification.ManuscriptAudit.FlatUnramifiedEtaleNeighborhood
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineLocalExtension
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineNormalStageStalk

/-! One common global affine étale neighbourhood carries all
specified sections of the actual weakly étale affine-line chart. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineGlobalStageFromModel

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap specMap)
open PrincipalDivisibilityLocus (divisibilityOpen mem_divisibilityOpen_iff)
open WeaklyEtaleAffineLineGenericStage (F)
open WeaklyEtaleAffineLineFiniteNormalization (model model_finite component_dedekind)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

variable {ι : Type u} (L : ι → Type u) [Finite ι]
  [∀ i, Field (L i)] [∀ i, Algebra (F K) (L i)]
  [∀ i, Algebra (R K) (L i)] [∀ i, IsScalarTower (R K) (F K) (L i)]
  [∀ i, Module.Finite (F K) (L i)] [∀ i, Algebra.IsSeparable (F K) (L i)]

set_option maxHeartbeats 3600000 in
/-- From one actual finite normal model and nonzero scalar multiples
of the tuple, construct one affine étale stage through which all
elements factor globally, including where their chosen denominators vanish. -/
theorem exists_stage (g : model K L →ₐ[R K] B) (hg : Function.Injective g)
    {κ : Type u} [Finite κ] (a : κ → R K) (d : κ → model K L) (z : κ → B)
    (ha : ∀ i, a i ≠ 0) (hEq : ∀ i, g (d i) = algebraMap (R K) B (a i) * z i) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (R K) C),
      Algebra.Etale (R K) C ∧ ∃ j : C →ₐ[R K] B, ∀ i, ∃ x : C, j x = z i := by
  let A := R K
  let D := model K L
  let φ := CommRingCat.ofHom (algebraMap A B)
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp
    ((Flat.SpecMap_iff (f := φ)).mp (inferInstanceAs (Flat (structureMap A B))))
  letI : Module.IsTorsionFree A D :=
    Function.Injective.moduleIsTorsionFree g hg (fun x y ↦ g.toLinearMap.map_smul x y)
  letI : Module.Flat A D := inferInstance
  letI : Module.Finite A D := model_finite K L
  letI : Algebra.FinitePresentation A D := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  let E : (ProetaleAffineTensor.spectrum D).Opens := ⟨Algebra.etaleLocus A D, Algebra.isOpen_etaleLocus⟩
  let V (i : κ) := divisibilityOpen (algebraMap A D (a i)) (d i)
  let U : (ProetaleAffineTensor.spectrum D).Opens := E ⊓ ⨅ i, V i
  have hU (p : PrimeSpectrum D) : p ∈ U ↔ p ∈ E ∧ ∀ i, p ∈ V i := by
    change p ∈ (U : Set (ProetaleAffineTensor.spectrum D)) ↔ _
    simp only [U, TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_iInf,
      Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
  have hAt (p : PrimeSpectrum B) : PrimeSpectrum.comap g.toRingHom p ∈ U := by
    let q := PrimeSpectrum.comap g.toRingHom p
    obtain ⟨hD, hVal, hUn⟩ :=
      WeaklyEtaleAffineLineNormalStageStalk.local_properties K B L g p.asIdeal
    letI : IsDomain (Localization.AtPrime q.asIdeal) := hD
    letI : ValuationRing (Localization.AtPrime q.asIdeal) := hVal
    letI : Algebra.IsUnramifiedAt A q.asIdeal := hUn
    apply (hU q).mpr
    constructor
    · have h₁ : (1 : D) ∉ q.asIdeal :=
        fun h ↦ q.isPrime.ne_top ((q.asIdeal.eq_top_iff_one).mpr h)
      obtain ⟨s, hs, _, hEt⟩ :=
        FlatUnramifiedEtaleNeighborhood.exists_etale_away A D q.asIdeal 1 h₁
      exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hEt)
        ((PrimeSpectrum.mem_basicOpen s q).mpr hs)
    · intro i
      obtain ⟨x, hx, _⟩ :=
        WeaklyEtaleAffineLineLocalExtension.exists_local_preimage_with_quotient
          g p.asIdeal q.asIdeal rfl (a i) (ha i) (d i) (z i) (hEq i)
      apply (mem_divisibilityOpen_iff _ _ q).mpr
      refine ⟨x, ?_⟩
      rw [← IsScalarTower.algebraMap_apply A D (Localization.AtPrime q.asIdeal)]
      exact hx.symm
  have hImage : Set.range (specMap A g) ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨specMap A g p, hAt p⟩, rfl⟩
  letI (i : ι) : IsDedekindDomain (integralClosure A (L i)) := component_dedekind K L i
  have hAff : IsAffineOpen U :=
    DedekindFiniteProductAffineOpen.isAffineOpen (fun i ↦ integralClosure A (L i)) U
  have hReg (i : κ) : IsLeftRegular (algebraMap A B (a i)) := by
    intro x y e
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero (ha i))
    simpa only [Algebra.smul_def] using e
  exact AffineOpenStageSections.exists_stage g U hAff hImage
    (fun p hp ↦ ((hU p).mp hp).1) a d z
    (fun i p hp ↦ ((hU p).mp hp).2 i) hReg hEq

end
end ManuscriptAudit.WeaklyEtaleAffineLineGlobalStageFromModel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineGlobalStageFromModel.exists_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
