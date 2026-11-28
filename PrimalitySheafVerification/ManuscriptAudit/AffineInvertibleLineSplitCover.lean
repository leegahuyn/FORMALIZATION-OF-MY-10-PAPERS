import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.PicardGroup
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverProduct

/-! An actual invertible affine line has a single affine étale splitting cover. -/

namespace ManuscriptAudit.AffineInvertibleLineSplitCover

open TensorProduct

noncomputable section

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

/-- A faithfully flat affine étale algebra together with a trivialization of
an actual scalar-extended affine line. -/
structure SplitCover where
  ring : Type
  [commRing : CommRing ring]
  [algebra : Algebra R ring]
  [etale : Algebra.Etale R ring]
  [faithfullyFlat : Module.FaithfullyFlat R ring]
  trivialization : ring ⊗[R] M ≃ₗ[ring] ring

variable {I : Type} [Fintype I] [DecidableEq I]
variable (B : I → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

private def productSplit (e : ∀ i, B i ⊗[R] M ≃ₗ[B i] B i) :
    (∀ i, B i) ⊗[R] M ≃ₗ[∀ i, B i] (∀ i, B i) := by
  let C := ∀ i, B i
  let r : C ⊗[R] M ≃ₗ[R] C :=
    (TensorProduct.comm R C M).trans
      ((TensorProduct.piRight R R M B).trans
        (LinearEquiv.piCongrRight fun i =>
          (TensorProduct.comm R M (B i)).trans ((e i).restrictScalars R)))
  have hTmul (c : C) (m : M) (i : I) : r (c ⊗ₜ[R] m) i = e i (c i ⊗ₜ[R] m) := by
    simp [r, TensorProduct.piRight_apply]
  refine { r.toEquiv with map_add' := r.map_add, map_smul' := ?_ }
  intro c z
  change r (c • z) = c • r z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [TensorProduct.smul_tmul']
    funext i
    change r ((c * a) ⊗ₜ[R] m) i = c i * r (a ⊗ₜ[R] m) i
    rw [hTmul, hTmul]
    change e i ((c i * a i) ⊗ₜ[R] m) = c i * e i (a i ⊗ₜ[R] m)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul] using (e i).map_smul (c i) (a i ⊗ₜ[R] m)
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

/-- A finite principal-open trivialization of an invertible module yields an actual
faithfully flat affine étale product algebra splitting the line. -/
theorem exists_splitCover [Module.Invertible R M] : Nonempty (SplitCover R M) := by
  classical
  obtain ⟨s, hs, hFree⟩ := Module.Invertible.exists_finset_free_localization R M
  let B (i : ↥s) := Localization.Away (i : R)
  letI : ∀ i, Algebra.Etale R (B i) := fun i =>
    Algebra.Etale.of_isLocalizationAway (i : R)
  have hCover (p : PrimeSpectrum R) :
      ∃ i : ↥s, ∃ q : PrimeSpectrum (B i), PrimeSpectrum.comap (algebraMap R (B i)) q = p := by
    have he : ∃ r ∈ s, r ∉ p.asIdeal := by
      by_contra! h
      have hc : Ideal.span (s : Set R) ≤ p.asIdeal := Ideal.span_le.mpr h
      rw [hs] at hc
      exact p.isPrime.ne_top (top_le_iff.mp hc)
    obtain ⟨r, hr, hp⟩ := he
    have hm : p ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := hp
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hm
    exact ⟨⟨r, hr⟩, hm⟩
  obtain ⟨hEt, hFF⟩ := AffineEtaleCoverProduct.product_affine_etale_faithfullyFlat B hCover
  let e (i : ↥s) : B i ⊗[R] M ≃ₗ[B i] B i :=
    let ee := (Module.Invertible.free_iff_linearEquiv.mp (hFree i i.property)).some
    ((IsLocalizedModule.isBaseChange (Submonoid.powers (i : R)) (B i)
      (LocalizedModule.mkLinearMap _ M)).equiv).trans ee
  exact ⟨{ ring := ∀ i, B i, commRing := inferInstance, algebra := inferInstance, etale := hEt,
    faithfullyFlat := hFF, trivialization := productSplit R M B e }⟩

end

end ManuscriptAudit.AffineInvertibleLineSplitCover

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineInvertibleLineSplitCover.exists_splitCover
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
