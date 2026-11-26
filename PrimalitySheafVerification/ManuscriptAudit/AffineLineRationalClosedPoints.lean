import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The rational closed points of the affine line

Every height-one prime of the polynomial ring over an algebraically
closed field is the kernel of evaluation at a unique scalar. The
corresponding geometric point is the actual spectrum map of evaluation.
-/

namespace ManuscriptAudit.AffineLineRationalClosedPoints

open AlgebraicGeometry IsDedekindDomain
open Polynomial

noncomputable section

variable (K : Type) [Field K]

private theorem linear_mem_eval_ker (a : K) :
    (X - C a : Polynomial K) ∈ RingHom.ker (evalRingHom a) := by
  simp [RingHom.mem_ker]

/-- The height-one prime of the closed point with coordinate `a`. -/
def closedPoint (a : K) : HeightOneSpectrum (Polynomial K) :=
  ⟨RingHom.ker (evalRingHom a), RingHom.ker_isPrime (evalRingHom a), by
    intro h
    exact X_sub_C_ne_zero a (Ideal.mem_bot.mp (h ▸ linear_mem_eval_ker K a))⟩

/-- The scheme point given by evaluation of the coordinate at `a`. -/
abbrev rationalPoint (a : K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  Spec.map (CommRingCat.ofHom (evalRingHom a))

/-- The point below the geometric map is the actual evaluation kernel. -/
theorem rationalPoint_default (a : K) :
    rationalPoint K a (default : Spec (CommRingCat.of K)) =
      (⟨(closedPoint K a).asIdeal, (closedPoint K a).isPrime⟩ : PrimeSpectrum (Polynomial K)) := by
  apply PrimeSpectrum.ext
  let x : Spec (CommRingCat.of K) := default
  letI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  let f : CommRingCat.of (Polynomial K) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (evalRingHom a)
  change (Spec.map f x).asIdeal = RingHom.ker (evalRingHom a)
  calc
    _ = Ideal.comap f.hom x.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal (Spec.map_apply f x)).trans
        (PrimeSpectrum.comap_asIdeal f.hom x)
    _ = _ := by
      rw [hx]
      exact (RingHom.ker_eq_comap_bot (evalRingHom a)).symm

/-- Every closed point has exactly one rational coordinate over an algebraically closed field. -/
theorem closedPoint_bijective [IsAlgClosed K] : Function.Bijective (closedPoint K) := by
  constructor
  · intro a b h
    have e : RingHom.ker (evalRingHom a) = RingHom.ker (evalRingHom b) :=
      congrArg HeightOneSpectrum.asIdeal h
    have hm : (X - C a : Polynomial K) ∈ RingHom.ker (evalRingHom b) :=
      e ▸ linear_mem_eval_ker K a
    have hab : b - a = 0 := by simpa [RingHom.mem_ker] using hm
    exact (sub_eq_zero.mp hab).symm
  · intro p
    letI : p.asIdeal.IsPrime := p.isPrime
    let g := Submodule.IsPrincipal.generator p.asIdeal
    have hg : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime p.asIdeal p.ne_bot
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root g (fun hd ↦ hg.not_unit
      (Polynomial.isUnit_iff_degree_eq_zero.mpr hd))
    have hle : p.asIdeal ≤ (closedPoint K a).asIdeal := by
      rw [← Ideal.span_singleton_generator p.asIdeal]
      refine Ideal.span_le.mpr ?_
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact ha
    have hp : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal p.isPrime p.ne_bot
    exact ⟨a, HeightOneSpectrum.ext (hp.eq_of_le (closedPoint K a).isPrime.ne_top hle).symm⟩

/-- Rational coordinates index the actual height-one primes of the affine line. -/
def closedPointEquiv [IsAlgClosed K] : K ≃ HeightOneSpectrum (Polynomial K) :=
  Equiv.ofBijective (closedPoint K) (closedPoint_bijective K)

end

end ManuscriptAudit.AffineLineRationalClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineRationalClosedPoints.rationalPoint_default,
      ``ManuscriptAudit.AffineLineRationalClosedPoints.closedPoint_bijective,
      ``ManuscriptAudit.AffineLineRationalClosedPoints.closedPointEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
