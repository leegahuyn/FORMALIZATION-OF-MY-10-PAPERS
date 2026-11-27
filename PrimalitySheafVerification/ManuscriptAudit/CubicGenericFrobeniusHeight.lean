import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericPointHeight
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSecantPoints
import PrimalitySheafVerification.ManuscriptAudit.RationalPowerHeight

/-! Relative Frobenius acts on the actual anti-invariant subgroup and scales its height. -/

namespace ManuscriptAudit.CubicGenericFrobeniusHeight

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open CubicGenericFunctionField CubicGenericAntiInvariant CubicGenericAbscissaPair CubicGenericPointHeight
open CubicFrobeniusSecantPoints CubicKummerSymmetricHeight RationalSubstitutionDegree RationalPowerHeight

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [Fintype K] (A : K)

private theorem map_comp (P : Points A) (f g : Model A →ₐ[K] Model A) :
    let h := centered_baseChange K (Model A) A
    pointMapAt K (Model A) (Curve A) (Curve (algebraMap K (Model A) A)) h f
      (pointMapAt K (Model A) (Curve A) (Curve (algebraMap K (Model A) A)) h g P) =
    pointMapAt K (Model A) (Curve A) (Curve (algebraMap K (Model A) A)) h (f.comp g) P := by
  let h := centered_baseChange K (Model A) A
  let mp := pointMapAt K (Model A) (Curve A) (Curve (algebraMap K (Model A) A)) h
  change mp f (mp g P) = mp (f.comp g) P
  cases P with
  | zero => simp
  | some x y hp =>
    obtain ⟨hg, eg⟩ := pointMapAt_some K (Model A) (Curve A) _ h g x y hp
    obtain ⟨hf, ef⟩ := pointMapAt_some K (Model A) (Curve A) _ h f (g x) (g y) hg
    obtain ⟨hfg, efg⟩ := pointMapAt_some K (Model A) (Curve A) _ h (f.comp g) x y hp
    change mp g (.some x y hp) = .some (g x) (g y) hg at eg
    change mp f (.some (g x) (g y) hg) = .some (f (g x)) (f (g y)) hf at ef
    change mp (f.comp g) (.some x y hp) = .some (f (g x)) (f (g y)) hfg at efg
    rw [eg, ef, efg]

/-- The quadratic involution commutes with relative Frobenius on the native point group. -/
theorem sigma_frobenius_comm (P : Points A) :
    sigma A (arithmeticPointFrobenius K (Model A) A P) =
      arithmeticPointFrobenius K (Model A) A (sigma A P) := by
  let f := FiniteField.frobeniusAlgHom K (Model A)
  let g := (conjugation A).restrictScalars K
  have he : g.comp f = f.comp g := by
    apply AlgHom.ext
    intro x
    change g (x ^ Fintype.card K) = (g x) ^ Fintype.card K
    exact map_pow g x _
  have h₁ := map_comp A P g f
  have h₂ := map_comp A P f g
  exact h₁.trans ((congrArg
    (fun r => pointMapAt K (Model A) (Curve A) (Curve (algebraMap K (Model A) A))
       (centered_baseChange K (Model A) A) r P) he).trans h₂.symm)

/-- The actual relative Frobenius preserves the anti-invariant subgroup. -/
def frobenius : antiInvariant A →+ antiInvariant A where
  toFun P := ⟨arithmeticPointFrobenius K (Model A) A P.val, by
    change sigma A (arithmeticPointFrobenius K (Model A) A P.val) =
      -(arithmeticPointFrobenius K (Model A) A P.val)
    rw [sigma_frobenius_comm, show sigma A P.val = -P.val from P.property, map_neg]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

/-- Actual relative Frobenius multiplies every rational abscissa height by q. -/
theorem height_frobenius (h₂ : (2 : K) ≠ 0) (P : antiInvariant A) :
    height A (frobenius A P) = Fintype.card K * height A P := by
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero =>
    change height A (frobenius A 0) = Fintype.card K * height A 0
    simp [height_zero]
  | some x y hp =>
    obtain ⟨hF, hFrob⟩ := actual_frobenius_some K (Model A) A x y hp
    let r := x.re
    have h₂' : (2 : RatFunc K) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr h₂
    have hx : algebraMap (RatFunc K) (Model A) r = x := by
      obtain ⟨u, hu⟩ := exists_algebraMap_of_fixed h₂' (abscissa_fixed A hP)
      have heu : u = r := congrArg QuadraticAlgebra.re hu
      rwa [heu] at hu
    have hxQ : (x ^ Fintype.card K).re = r ^ Fintype.card K := by
      have hQ : algebraMap (RatFunc K) (Model A) (r ^ Fintype.card K) = x ^ Fintype.card K := by
        rw [map_pow, hx]
      exact (congrArg QuadraticAlgebra.re hQ).symm
    change pairHeight (polynomialPair A
      (arithmeticPointFrobenius K (Model A) A (.some x y hp))) =
      Fintype.card K * pairHeight (polynomialPair A (.some x y hp))
    rw [hFrob]
    change rationalDegree ((x ^ Fintype.card K).re) = Fintype.card K * rationalDegree r
    rw [hxQ, degree_pow]

/-- The generic point itself has height one. -/
theorem genericPoint_height (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    height A ⟨genericPoint A h₂ h₃ hA, genericPoint_mem_antiInvariant A h₂ h₃ hA⟩ = 1 := by
  change rationalDegree (RatFunc.X : RatFunc K) = 1
  simpa only [pow_one] using (degree_X_pow (K := K) 1)

end

end ManuscriptAudit.CubicGenericFrobeniusHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericFrobeniusHeight.sigma_frobenius_comm,
      ``ManuscriptAudit.CubicGenericFrobeniusHeight.height_frobenius,
      ``ManuscriptAudit.CubicGenericFrobeniusHeight.genericPoint_height] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
