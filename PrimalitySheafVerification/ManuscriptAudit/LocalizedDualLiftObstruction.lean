import Lean.Util.CollectAxioms
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Unramified.Basic

/-! Two distinct first-order lifts stay distinct on the local ring at their common residue point. -/

namespace ManuscriptAudit.LocalizedDualLiftObstruction

open scoped DualNumber

noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem not_formally_unramified_of_local_lifts (v : A →ₐ[K] K) (P : Ideal A) [P.IsPrime]
    (hP : P = RingHom.ker v.toRingHom) (S : Type*) [CommRing S]
    [Algebra K S] [Algebra A S] [IsScalarTower K A S] [IsLocalization P.primeCompl S]
    (a b : A →ₐ[K] K[ε])
    (ha : (TrivSqZeroExt.fstHom K K K).comp a = v)
    (hb : (TrivSqZeroExt.fstHom K K K).comp b = v) (hNe : a ≠ b) :
    ¬ Algebra.FormallyUnramified K S := by
  intro hUnramified
  letI : Algebra.FormallyUnramified K S := hUnramified
  let r : K[ε] →ₐ[K] K := TrivSqZeroExt.fstHom K K K
  have hUnit (f : A →ₐ[K] K[ε]) (h : r.comp f = v) (x : P.primeCompl) : IsUnit (f x) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    change IsUnit (r (f x))
    rw [show r (f x) = v x from AlgHom.congr_fun h x]
    apply isUnit_iff_ne_zero.mpr
    intro hz
    let u : A := x
    have hup : u ∉ P := Ideal.mem_primeCompl_iff.mp x.2
    have huk : u ∈ RingHom.ker v.toRingHom := RingHom.mem_ker.mpr hz
    exact hup (Eq.mpr (congrArg (fun J : Ideal A => u ∈ J) hP) huk)
  let aS : S →ₐ[K] K[ε] := IsLocalization.liftAlgHom (hUnit a ha)
  let bS : S →ₐ[K] K[ε] := IsLocalization.liftAlgHom (hUnit b hb)
  have haS (x : A) : aS (algebraMap A S x) = a x :=
    IsLocalization.lift_eq (M := P.primeCompl) (hUnit a ha) x
  have hbS (x : A) : bS (algebraMap A S x) = b x :=
    IsLocalization.lift_eq (M := P.primeCompl) (hUnit b hb) x
  have hSame : r.comp aS = r.comp bS := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext P.primeCompl
    ext x
    change r (aS (algebraMap A S x)) = r (bS (algebraMap A S x))
    rw [haS x, hbS x]
    exact (AlgHom.congr_fun ha x).trans (AlgHom.congr_fun hb x).symm
  have hNil : IsNilpotent (RingHom.ker r.toRingHom) := ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩
  have hMaps := Algebra.FormallyUnramified.lift_unique' r hNil aS bS hSame
  apply hNe
  apply AlgHom.ext
  intro x
  exact (haS x).symm.trans ((AlgHom.congr_fun hMaps (algebraMap A S x)).trans (hbS x))

end

end ManuscriptAudit.LocalizedDualLiftObstruction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.LocalizedDualLiftObstruction.not_formally_unramified_of_local_lifts
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
