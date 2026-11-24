import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic

namespace ManuscriptAudit.BenchmarkCusp

noncomputable section

open MvPolynomial

private abbrev k := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev Plane := MvPolynomial (Fin 2) k
private abbrev equation : Plane := X 0 ^ 2 + X 1 ^ 3
private abbrev equationIdeal : Ideal Plane := Ideal.span {equation}

/-- The coordinate ring of the benchmark \(x^2+y^3=0\) over \(\mathbb F_5\). -/
abbrev CuspRing := Plane ⧸ equationIdeal

private abbrev coord (i : Fin 2) : CuspRing :=
  Ideal.Quotient.mk equationIdeal (X i)

private theorem coord_relation : coord 0 ^ 2 + coord 1 ^ 3 = 0 := by
  change Ideal.Quotient.mk equationIdeal (X 0) ^ 2 +
    Ideal.Quotient.mk equationIdeal (X 1) ^ 3 = 0
  rw [← map_pow, ← map_pow, ← map_add]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self equation)

private def evalOrigin : Plane →ₐ[k] k :=
  aeval (fun _ : Fin 2 => (0 : k))

private theorem liftEquation {B : Type} [CommRing B] [Algebra k B]
    (f : Plane →ₐ[k] B) (hf : f equation = 0) :
    ∀ g : Plane, g ∈ equationIdeal → f g = 0 := by
  intro g hg
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hg
  rw [map_mul, hf, zero_mul]

/-- The residue map at the origin. -/
def atOrigin : CuspRing →ₐ[k] k :=
  Ideal.Quotient.liftₐ equationIdeal evalOrigin
    (liftEquation evalOrigin (by simp [evalOrigin, equation]))

/-- The prime of the geometric benchmark corresponding to the rational origin. -/
abbrev originIdeal : Ideal CuspRing := RingHom.ker atOrigin.toRingHom

instance originIdeal_isPrime : originIdeal.IsPrime :=
  RingHom.ker_isPrime atOrigin.toRingHom

private abbrev CuspLocal := Localization.AtPrime originIdeal

private abbrev P := Polynomial k
private abbrev I₃ : Ideal P := Ideal.span {(Polynomial.X : P) ^ 3}
private abbrev T := P ⧸ I₃
private abbrev qT : P →ₐ[k] T := Ideal.Quotient.mkₐ k I₃
private abbrev t : T := qT Polynomial.X

private theorem t_cube : t ^ 3 = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

private theorem t_square_ne_zero : t ^ 2 ≠ 0 := by
  intro h
  rw [← map_pow] at h
  have hdvd : (Polynomial.X : P) ^ 3 ∣ Polynomial.X ^ 2 :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdvd) 2 (by decide)
  exact one_ne_zero (by simpa using hcoeff : (1 : k) = 0)

private abbrev J : Ideal T := Ideal.span {t ^ 2}
private abbrev U := T ⧸ J
private abbrev qU : T →ₐ[k] U := Ideal.Quotient.mkₐ k J
private abbrev qP : P →ₐ[k] U := qU.comp qT

private theorem J_square : J ^ 2 = ⊥ := by
  have hfour : (t ^ 2) ^ 2 = 0 := by
    calc
      (t ^ 2) ^ 2 = t ^ 3 * t := by ring
      _ = 0 := by rw [t_cube, zero_mul]
  rw [Ideal.span_singleton_pow, hfour]
  simp

private theorem mul_t_eq_zero_of_mem_J {z : T} (hz : z ∈ J) : t * z = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hz
  calc
    t * (t ^ 2 * a) = t ^ 3 * a := by ring
    _ = 0 := by rw [t_cube, zero_mul]

private theorem square_eq_zero_of_mem_J {z : T} (hz : z ∈ J) : z ^ 2 = 0 := by
  have hm : z * z ∈ J * J := Ideal.mul_mem_mul hz hz
  rw [← pow_two J, J_square, Ideal.mem_bot] at hm
  simpa only [pow_two] using hm

private theorem qP_X_square : (qP Polynomial.X) ^ 2 = 0 := by
  change (qU t) ^ 2 = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

private def firstCoordinate : Plane →ₐ[k] P :=
  aeval (fun i : Fin 2 => if i = 0 then Polynomial.X else 0)

private theorem firstCoordinate_zero : firstCoordinate (X 0) = Polynomial.X := by
  simp [firstCoordinate]

private theorem firstCoordinate_one : firstCoordinate (X 1) = 0 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [firstCoordinate, h]

private theorem const_firstCoordinate (g : Plane) :
    (firstCoordinate g).coeff 0 = evalOrigin g := by
  have he : (Polynomial.aeval (0 : k)).comp firstCoordinate = evalOrigin := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [evalOrigin, firstCoordinate_zero, firstCoordinate_one]
  rw [Polynomial.coeff_zero_eq_aeval_zero]
  exact AlgHom.congr_fun he g

private def intoU : CuspRing →ₐ[k] U :=
  Ideal.Quotient.liftₐ equationIdeal (qP.comp firstCoordinate)
    (liftEquation (qP.comp firstCoordinate) (by
      simp [equation, firstCoordinate_zero, firstCoordinate_one, qP_X_square]))

private theorem intoU_x : intoU (coord 0) = qU t := by
  change qP (firstCoordinate (X 0)) = qU t
  simpa only [firstCoordinate_zero]

private theorem intoU_y : intoU (coord 1) = 0 := by
  change qP (firstCoordinate (X 1)) = 0
  rw [firstCoordinate_one, map_zero]

private theorem qP_isUnit (g : P) (h : g.coeff 0 ≠ 0) : IsUnit (qP g) := by
  obtain ⟨a, ha⟩ := Polynomial.X_dvd_sub_C g
  have he : qP g - qP (Polynomial.C (g.coeff 0)) = qP Polynomial.X * qP a := by
    simpa only [map_sub, map_mul] using congrArg qP ha
  have hn : IsNilpotent (qP g - qP (Polynomial.C (g.coeff 0))) := by
    use 2
    rw [he, mul_pow, qP_X_square, zero_mul]
  have hc : IsUnit (qP (Polynomial.C (g.coeff 0))) :=
    ((isUnit_iff_ne_zero.mpr h).map Polynomial.C).map qP.toRingHom
  simpa using hn.isUnit_add_right_of_commute hc (Commute.all _ _)

private theorem intoU_unit (s : originIdeal.primeCompl) : IsUnit (intoU s) := by
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (I := equationIdeal) (s : CuspRing)
  have hres : (firstCoordinate g).coeff 0 ≠ 0 := by
    rw [const_firstCoordinate]
    have hn : atOrigin (s : CuspRing) ≠ 0 := s.property
    rw [← hg] at hn
    exact hn
  change IsUnit (intoU (s : CuspRing))
  rw [← hg]
  exact qP_isUnit (firstCoordinate g) hres

private def localMap : CuspLocal →ₐ[k] U :=
  IsLocalization.liftAlgHom (f := intoU) intoU_unit

private theorem localMap_on_ring (a : CuspRing) :
    localMap (algebraMap CuspRing CuspLocal a) = intoU a := by
  exact IsLocalization.lift_eq (g := intoU.toRingHom) intoU_unit a

/-- Paper 2, PDF pp. 29 and 44–49. The cusp \(x^2+y^3\) remains
non-smooth at the actual origin of its fiber over \(\mathbb F_5\).
The map sending \(x\) to \(t\) and \(y\) to zero in \(k[t]/(t^2)\)
extends to the origin localization. It cannot lift through the
square-zero thickening \(k[t]/(t^3)\). -/
theorem cusp_not_smooth_at_origin : ¬ Algebra.IsSmoothAt k originIdeal := by
  intro hs
  letI : Algebra.FormallySmooth k CuspLocal := hs
  obtain ⟨lift, hlift⟩ := Algebra.FormallySmooth.comp_surjective
    k CuspLocal J J_square localMap
  let x := algebraMap CuspRing CuspLocal (coord 0)
  let y := algebraMap CuspRing CuspLocal (coord 1)
  have hx : qU (lift x) = qU t := by
    have h := AlgHom.congr_fun hlift x
    change qU (lift x) = localMap x at h
    rw [h, localMap_on_ring, intoU_x]
  have hy : qU (lift y) = 0 := by
    have h := AlgHom.congr_fun hlift y
    change qU (lift y) = localMap y at h
    rw [h, localMap_on_ring, intoU_y]
  let d := lift x - t
  have hd : d ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qU d = 0
    rw [show d = lift x - t from rfl, map_sub, hx, sub_self]
  have hymem : lift y ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hy3 : (lift y) ^ 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ,
      square_eq_zero_of_mem_J hymem, zero_mul]
  have hx2 : (lift x) ^ 2 = t ^ 2 := by
    have hex : lift x = t + d := by
      change lift x = t + (lift x - t)
      ring
    conv_lhs => rw [hex]
    calc
      (t + d) ^ 2 = t ^ 2 + 2 * (t * d) + d ^ 2 := by ring
      _ = t ^ 2 := by
        simp [mul_t_eq_zero_of_mem_J hd, square_eq_zero_of_mem_J hd]
  have hrel : x ^ 2 + y ^ 3 = 0 := by
    change (algebraMap CuspRing CuspLocal (coord 0)) ^ 2 +
      (algebraMap CuspRing CuspLocal (coord 1)) ^ 3 = 0
    rw [← map_pow, ← map_pow, ← map_add, coord_relation, map_zero]
  have h := congrArg lift hrel
  rw [map_add, map_pow, map_pow, map_zero, hx2, hy3, add_zero] at h
  exact t_square_ne_zero h

/-- At the prime five, the printed benchmark factor \(2\cdot 3\) is a unit,
while the benchmark fiber is singular at the origin. -/
theorem benchmark_delta_unit_and_singular :
    IsUnit (((2 : ℕ) * 3 : ℕ) : ZMod 5) ∧
      ¬ Algebra.IsSmoothAt (ZMod 5) originIdeal := by
  exact ⟨isUnit_iff_ne_zero.mpr (by decide), cusp_not_smooth_at_origin⟩

end

end ManuscriptAudit.BenchmarkCusp

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.BenchmarkCusp.cusp_not_smooth_at_origin,
    ``ManuscriptAudit.BenchmarkCusp.benchmark_delta_unit_and_singular] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
