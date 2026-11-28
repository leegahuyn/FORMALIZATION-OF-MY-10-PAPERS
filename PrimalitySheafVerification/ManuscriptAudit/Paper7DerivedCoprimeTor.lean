import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.QuotientRing
import PrimalitySheafVerification.ManuscriptAudit.Paper7DerivedTorCRT
import PrimalitySheafVerification.ManuscriptAudit.IntCyclicDerivedTor

/-! The actual degree-one derived obstruction vanishes in the coprime
regime and decomposes for the literal product of coprime integer powers. -/

namespace ManuscriptAudit.Paper7DerivedCoprimeTor

open CategoryTheory CategoryTheory.Limits Function
open IntCyclicProjectiveResolution (ideal residues)
open scoped BigOperators

noncomputable section

private abbrev C := ModuleCat.{0} ℤ

/-- This is precisely the genuine CRT decomposition at the product of
the integral factor powers. -/
def torOneProductIso {ι : Type} [Fintype ι] (f : ι → ℕ)
    (hc : Pairwise (Nat.Coprime on f)) (m : ℕ) :
    ((Tor C 1).obj (residues m)).obj (residues (∏ j, f j)) ≅
      ⨁ fun j ↦ ((Tor C 1).obj (residues m)).obj (residues (f j)) := by
  have he : (⨅ j, ideal (f j)) = ideal (∏ j, f j) :=
    Ideal.iInf_span_singleton_natCast (R := ℤ) hc
  have hh : Pairwise (IsCoprime on (ideal ∘ f)) := fun i j hij ↦
    (Ideal.isCoprime_span_singleton_iff _ _).mpr ((hc hij).cast (R := ℤ))
  change ((Tor C 1).obj (residues m)).obj (ModuleCat.of ℤ (ℤ ⧸ ideal (∏ j, f j))) ≅ _
  rw [← he]
  exact Paper7DerivedTorCRT.torCRTIso (ideal ∘ f) hh 1 (residues m)

private def residueLinear (m : ℕ) : (ℤ ⧸ ideal m) ≃ₗ[ℤ] ZMod m where
  __ := (Int.quotientSpanNatEquivZMod m).toAddEquiv
  map_smul' a x := map_zsmul _ _ _

/-- In the coprime regime the actual tensor-derived Tor₁ object is zero.
The scalar action on the concrete coefficient module is a unit. -/
theorem torOne_coprime_isZero (m n : ℕ) (hn : n ≠ 0) (hc : m.Coprime n) :
    IsZero (((Tor C 1).obj (residues m)).obj (residues n)) := by
  let E := (residueLinear m).toModuleIso
  let F := Tor C 1
  let A := ModuleCat.of ℤ (ZMod m)
  have hZ : IsZero (((Tor C 1).obj A).obj (residues n)) := by
    apply (Iso.isZero_iff (IntCyclicDerivedTor.torOneEquivKernel A n hn)).mpr
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    apply Subtype.ext
    have hx : (n : ZMod m) * x.val = 0 := by
      simpa using x.property
    have hu : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr hc.symm
    exact (hu.mul_left_cancel (hx.trans (mul_zero _).symm))
  exact (Iso.isZero_iff ((F.mapIso E).app (residues n))).mpr hZ

end
end ManuscriptAudit.Paper7DerivedCoprimeTor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper7DerivedCoprimeTor.torOneProductIso,
      ``ManuscriptAudit.Paper7DerivedCoprimeTor.torOne_coprime_isZero] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
