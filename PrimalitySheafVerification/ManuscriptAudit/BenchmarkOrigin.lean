import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic

/-!
Paper 2, physical pp. 44–45, §5.5 studies the fibers of x^(pₙ)+y^A=0
for exponents pₙ,A at least two. The origin is singular in every
characteristic, including on the base open D(Apₙ). The proof uses an
explicit square-zero lifting obstruction at the origin.
-/

namespace ManuscriptAudit.BenchmarkOrigin

noncomputable section

open MvPolynomial

variable (K : Type*) [Field K]

private abbrev Plane := MvPolynomial (Fin 2) K
private abbrev equation (r s : ℕ) : Plane K := X 0 ^ r + X 1 ^ s
private abbrev equationIdeal (r s : ℕ) : Ideal (Plane K) := Ideal.span {equation K r s}

/-- The fiber's coordinate ring with exponents r and s. -/
abbrev CurveRing (r s : ℕ) := Plane K ⧸ equationIdeal K r s

private abbrev coord (r s : ℕ) (i : Fin 2) : CurveRing K r s :=
  Ideal.Quotient.mk (equationIdeal K r s) (X i)

private theorem coord_relation (r s : ℕ) : coord K r s 0 ^ r + coord K r s 1 ^ s = 0 := by
  change Ideal.Quotient.mk (equationIdeal K r s) (X 0) ^ r +
    Ideal.Quotient.mk (equationIdeal K r s) (X 1) ^ s = 0
  rw [← map_pow, ← map_pow, ← map_add]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

private def evalOrigin : Plane K →ₐ[K] K := aeval (fun _ : Fin 2 => (0 : K))

private theorem liftEquation (r s : ℕ) {B : Type*} [CommRing B] [Algebra K B]
    (f : Plane K →ₐ[K] B) (hf : f (equation K r s) = 0) :
    ∀ g : Plane K, g ∈ equationIdeal K r s → f g = 0 := by
  intro g hg
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hg
  rw [map_mul, hf, zero_mul]

private def descendEquation (r s : ℕ) {B : Type*} [CommRing B] [Algebra K B]
    (f : Plane K →ₐ[K] B) (hf : f (equation K r s) = 0) :
    CurveRing K r s →ₐ[K] B :=
  Ideal.Quotient.liftₐ (equationIdeal K r s) f (liftEquation K r s f hf)

private theorem descendEquation_mk (r s : ℕ) {B : Type*} [CommRing B] [Algebra K B]
    (f : Plane K →ₐ[K] B) (hf : f (equation K r s) = 0) (g : Plane K) :
    descendEquation K r s f hf (Ideal.Quotient.mk (equationIdeal K r s) g) = f g := rfl

/-- Evaluation at the origin of the benchmark fiber. -/
def atOrigin {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) : CurveRing K r s →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (evalOrigin K)
    (liftEquation K r s (evalOrigin K) (by
      have hr₀ : r ≠ 0 := by omega
      have hs₀ : s ≠ 0 := by omega
      simp [evalOrigin, equation, zero_pow hr₀, zero_pow hs₀]))

/-- The prime corresponding to the rational origin. -/
abbrev originIdeal {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) : Ideal (CurveRing K r s) :=
  RingHom.ker (atOrigin K hr hs).toRingHom

instance originIdeal_isPrime {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    (originIdeal K hr hs).IsPrime :=
  RingHom.ker_isPrime (atOrigin K hr hs).toRingHom

private abbrev Local {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :=
  Localization.AtPrime (originIdeal K hr hs)

private abbrev P := Polynomial K
private abbrev T (r : ℕ) := P K ⧸ Ideal.span {(Polynomial.X : P K) ^ (r + 1)}
private abbrev qT (r : ℕ) : P K →ₐ[K] T K r := Ideal.Quotient.mkₐ K _
private abbrev t (r : ℕ) : T K r := qT K r Polynomial.X

private theorem t_top_power (r : ℕ) : (t K r) ^ (r + 1) = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

private theorem t_lower_power_ne_zero (r : ℕ) : (t K r) ^ r ≠ 0 := by
  intro h
  rw [← map_pow] at h
  have hdvd : (Polynomial.X : P K) ^ (r + 1) ∣ Polynomial.X ^ r :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdvd) r (by omega)
  exact one_ne_zero (by simpa using hcoeff : (1 : K) = 0)

private abbrev J (r : ℕ) : Ideal (T K r) := Ideal.span {(t K r) ^ r}
private abbrev U (r : ℕ) := T K r ⧸ J K r
private abbrev qU (r : ℕ) : T K r →ₐ[K] U K r := Ideal.Quotient.mkₐ K _
private abbrev qP (r : ℕ) : P K →ₐ[K] U K r := (qU K r).comp (qT K r)

private theorem J_square {r : ℕ} (hr : 2 ≤ r) : (J K r) ^ 2 = ⊥ := by
  have hzero : ((t K r) ^ r) ^ 2 = 0 := by
    rw [← pow_mul, show r * 2 = (r + 1) + (r - 1) by omega, pow_add,
      t_top_power K r, zero_mul]
  rw [Ideal.span_singleton_pow, hzero]
  simp

private theorem mul_t_eq_zero_of_mem_J {r : ℕ} {z : T K r} (hz : z ∈ J K r) :
    t K r * z = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hz
  calc
    t K r * ((t K r) ^ r * a) = ((t K r) ^ r * t K r) * a := by ac_rfl
    _ = (t K r) ^ (r + 1) * a :=
      congrArg (fun z : T K r => z * a) (pow_succ (t K r) r).symm
    _ = 0 := by rw [t_top_power K r, zero_mul]

private theorem square_eq_zero_of_mem_J {r : ℕ} (hr : 2 ≤ r) {z : T K r}
    (hz : z ∈ J K r) : z ^ 2 = 0 := by
  have hm : z * z ∈ (J K r) * (J K r) := Ideal.mul_mem_mul hz hz
  rw [← pow_two (J K r), J_square K hr, Ideal.mem_bot] at hm
  simpa only [pow_two] using hm

private theorem qP_X_pow (r : ℕ) : (qP K r Polynomial.X) ^ r = 0 := by
  change ((qU K r) (t K r)) ^ r = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

private def firstCoordinate : Plane K →ₐ[K] P K :=
  aeval (fun i : Fin 2 => if i = 0 then Polynomial.X else 0)

private theorem firstCoordinate_zero : firstCoordinate K (X 0) = Polynomial.X := by
  simp [firstCoordinate]

private theorem firstCoordinate_one : firstCoordinate K (X 1) = 0 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [firstCoordinate, h]

private theorem const_firstCoordinate (g : Plane K) :
    (firstCoordinate K g).coeff 0 = evalOrigin K g := by
  have he : (Polynomial.aeval (0 : K)).comp (firstCoordinate K) = evalOrigin K := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [evalOrigin, firstCoordinate_zero, firstCoordinate_one]
  rw [Polynomial.coeff_zero_eq_aeval_zero]
  exact AlgHom.congr_fun he g

private def composedEval (r : ℕ) : Plane K →ₐ[K] U K r :=
  (qP K r).comp (firstCoordinate K)

private theorem composedEval_equation {r s : ℕ} (hs : 2 ≤ s) :
    composedEval K r (equation K r s) = 0 := by
  have hs₀ : s ≠ 0 := by omega
  have he : firstCoordinate K (equation K r s) = (Polynomial.X : P K) ^ r := by
    simp [equation, firstCoordinate_zero, firstCoordinate_one, zero_pow hs₀]
  calc
    composedEval K r (equation K r s) = qP K r (firstCoordinate K (equation K r s)) := rfl
    _ = qP K r ((Polynomial.X : P K) ^ r) := congrArg (qP K r) he
    _ = (qP K r Polynomial.X) ^ r := map_pow (qP K r) Polynomial.X r
    _ = 0 := qP_X_pow K r

private def intoU {r s : ℕ} (hs : 2 ≤ s) : CurveRing K r s →ₐ[K] U K r :=
  descendEquation K r s (B := U K r) (composedEval K r) (composedEval_equation K (r := r) hs)

private theorem intoU_mk {r s : ℕ} (hs : 2 ≤ s) (g : Plane K) :
    intoU K (r := r) hs (Ideal.Quotient.mk (equationIdeal K r s) g) =
      qP K r (firstCoordinate K g) :=
  descendEquation_mk K r s (B := U K r) (composedEval K r)
    (composedEval_equation K (r := r) hs) g

private theorem intoU_x {r s : ℕ} (hs : 2 ≤ s) :
    intoU K (r := r) hs (coord K r s 0) = qU K r (t K r) := by
  calc
    intoU K (r := r) hs (coord K r s 0) = qP K r (firstCoordinate K (X 0)) :=
      intoU_mk K hs _
    _ = qP K r Polynomial.X := congrArg (qP K r) (firstCoordinate_zero K)
    _ = qU K r (t K r) := rfl

private theorem intoU_y {r s : ℕ} (hs : 2 ≤ s) :
    intoU K (r := r) hs (coord K r s 1) = 0 := by
  calc
    intoU K (r := r) hs (coord K r s 1) = qP K r (firstCoordinate K (X 1)) :=
      intoU_mk K hs _
    _ = qP K r 0 := congrArg (qP K r) (firstCoordinate_one K)
    _ = 0 := map_zero (qP K r)

private theorem qP_isUnit {r : ℕ} (g : P K) (h : g.coeff 0 ≠ 0) :
    IsUnit (qP K r g) := by
  have hdvd : (Polynomial.X : P K) ∣ g - Polynomial.C (g.coeff 0) :=
    Polynomial.X_dvd_sub_C
  obtain ⟨a, ha⟩ := hdvd
  have he : qP K r g - qP K r (Polynomial.C (g.coeff 0)) =
      qP K r Polynomial.X * qP K r a := by
    simpa only [map_sub, map_mul] using congrArg (qP K r) ha
  have hn : IsNilpotent (qP K r g - qP K r (Polynomial.C (g.coeff 0))) := by
    use r
    rw [he]
    have hcomm : Commute (qP K r Polynomial.X) (qP K r a) := by
      change qP K r Polynomial.X * qP K r a = qP K r a * qP K r Polynomial.X
      simpa only [map_mul] using
        congrArg (qP K r) (mul_comm (Polynomial.X : P K) a)
    calc
      _ = (qP K r Polynomial.X) ^ r * (qP K r a) ^ r := hcomm.mul_pow r
      _ = (0 : U K r) * (qP K r a) ^ r :=
        congrArg (fun z : U K r => z * (qP K r a) ^ r) (qP_X_pow K r)
      _ = 0 := by
        simpa only [map_mul, map_zero, map_pow] using congrArg (qP K r) (zero_mul (a ^ r))
  have hc : IsUnit (qP K r (Polynomial.C (g.coeff 0))) :=
    ((isUnit_iff_ne_zero.mpr h).map Polynomial.C).map (qP K r).toRingHom
  have hcomm : Commute (qP K r g - qP K r (Polynomial.C (g.coeff 0)))
      (qP K r (Polynomial.C (g.coeff 0))) := by
    change (qP K r g - qP K r (Polynomial.C (g.coeff 0))) *
        qP K r (Polynomial.C (g.coeff 0)) =
      qP K r (Polynomial.C (g.coeff 0)) * (qP K r g - qP K r (Polynomial.C (g.coeff 0)))
    simpa only [map_sub, map_mul] using congrArg (qP K r)
      (mul_comm (g - Polynomial.C (g.coeff 0)) (Polynomial.C (g.coeff 0)))
  simpa using hn.isUnit_add_right_of_commute hc hcomm

private theorem intoU_unit {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (u : (originIdeal K hr hs).primeCompl) : IsUnit (intoU K (r := r) hs u) := by
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (I := equationIdeal K r s) (u : CurveRing K r s)
  have hres : (firstCoordinate K g).coeff 0 ≠ 0 := by
    rw [const_firstCoordinate]
    have hn : atOrigin K hr hs (u : CurveRing K r s) ≠ 0 := u.property
    rw [← hg] at hn
    exact hn
  change IsUnit (intoU K (r := r) hs (u : CurveRing K r s))
  rw [← hg, intoU_mk]
  exact qP_isUnit K (firstCoordinate K g) hres

private def localMap {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    Local K hr hs →ₐ[K] U K r :=
  IsLocalization.liftAlgHom (A := K) (R := CurveRing K r s)
    (M := (originIdeal K hr hs).primeCompl) (S := Local K hr hs)
    (P := U K r) (f := intoU K (r := r) hs) (intoU_unit K hr hs)

private theorem localMap_on_ring {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (a : CurveRing K r s) :
    localMap K hr hs (algebraMap (CurveRing K r s) (Local K hr hs) a) = intoU K (r := r) hs a := by
  simp only [localMap, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq] <;> rfl

private theorem pow_add_eq_of_annihilated {B : Type*} [CommRing B] {x d : B}
    (hxd : x * d = 0) (hd : d ^ 2 = 0) {r : ℕ} (hr : 2 ≤ r) :
    (x + d) ^ r = x ^ r := by
  induction r, hr using Nat.le_induction with
  | base =>
      calc
        (x + d) ^ 2 = x ^ 2 + 2 * (x * d) + d ^ 2 := by ring
        _ = x ^ 2 := by simp [hxd, hd]
  | succ r hr ih =>
      have hpow : x ^ r * d = 0 := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 1 ≤ r by omega)
        rw [hm, add_comm 1 m, pow_add, pow_one, mul_assoc, hxd, mul_zero]
      calc
        (x + d) ^ (r + 1) = x ^ r * (x + d) := by rw [pow_succ, ih]
        _ = x ^ (r + 1) := by rw [mul_add, hpow, add_zero, pow_succ]

/-- The actual benchmark fiber is singular at its origin in every characteristic. -/
theorem paper2_benchmark_not_smooth_at_origin {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ Algebra.IsSmoothAt K (originIdeal K hr hs) := by
  intro hSmooth
  letI : Algebra.FormallySmooth K (Local K hr hs) := hSmooth
  obtain ⟨lift, hlift⟩ := Algebra.FormallySmooth.comp_surjective
    K (Local K hr hs) (J K r) (J_square K hr) (localMap K hr hs)
  let x := algebraMap (CurveRing K r s) (Local K hr hs) (coord K r s 0)
  let y := algebraMap (CurveRing K r s) (Local K hr hs) (coord K r s 1)
  have hx : qU K r (lift x) = qU K r (t K r) := by
    have h := AlgHom.congr_fun hlift x
    change qU K r (lift x) = localMap K hr hs x at h
    rw [h, localMap_on_ring K hr hs, intoU_x K hs]
  have hy : qU K r (lift y) = 0 := by
    have h := AlgHom.congr_fun hlift y
    change qU K r (lift y) = localMap K hr hs y at h
    rw [h, localMap_on_ring K hr hs, intoU_y K hs]
  let d := lift x - t K r
  have hd : d ∈ J K r := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qU K r d = 0
    rw [show d = lift x - t K r from rfl, map_sub, hx, sub_self]
  have hymem : lift y ∈ J K r := Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hyS : (lift y) ^ s = 0 :=
    pow_eq_zero_of_le hs (square_eq_zero_of_mem_J K hr hymem)
  have hxR : (lift x) ^ r = (t K r) ^ r := by
    have hxd : lift x = t K r + d := by
      change lift x = t K r + (lift x - t K r)
      ring
    rw [hxd]
    exact pow_add_eq_of_annihilated (mul_t_eq_zero_of_mem_J K hd)
      (square_eq_zero_of_mem_J K hr hd) hr
  have hrel : x ^ r + y ^ s = 0 := by
    simpa only [map_add, map_pow, map_zero] using
      congrArg (algebraMap (CurveRing K r s) (Local K hr hs)) (coord_relation K r s)
  have h := congrArg lift hrel
  rw [map_add, map_pow, map_pow, map_zero, hxR, hyS, add_zero] at h
  exact t_lower_power_ne_zero K r h

/-- The benchmark's base factor may be a unit in the residue field even though
the fiber at that prime is singular at the actual origin. -/
theorem paper2_benchmark_base_open_and_singular {p r s : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hp : ¬ p ∣ r * s) :
    IsUnit ((r * s : ℕ) : ZMod p) ∧
      ¬ Algebra.IsSmoothAt (ZMod p) (originIdeal (ZMod p) hr hs) := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_, paper2_benchmark_not_smooth_at_origin (ZMod p) hr hs⟩
  intro h
  exact hp ((ZMod.natCast_eq_zero_iff (r * s) p).1 h)

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``paper2_benchmark_not_smooth_at_origin, ``paper2_benchmark_base_open_and_singular] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.BenchmarkOrigin
