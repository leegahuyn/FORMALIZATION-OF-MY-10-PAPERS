import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportHZero
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportLowDegrees

/-!
# The actual extra degree-one compact-support contribution

Both degree-zero groups vanish on the two dense open parts of the
proper cusp. The rational origin maps isomorphically onto the kernel
of the map from puncture Hc¹ to cusp Hc¹. This gives the relative
degree-one contribution without assuming that the two ambient groups
are finite-dimensional.
-/

namespace ManuscriptAudit.CuspCompactSupportExcess

open CategoryTheory CategoryTheory.Abelian
open CuspCompactSupportSequence CuspCompactSupportLowDegrees

universe u

noncomputable section

variable (K : Type u) [Field K] [IsSepClosed K]

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev boundarySections (M : AddCommGrpCat.{u}) :=
  Sheaf.H (compactSupportSequence K M).X₃ 0

private abbrev firstComparison (M : AddCommGrpCat.{u}) :
    punctureHc K M 1 →+ cuspHc K M 1 :=
  Sheaf.H.map (compactSupportSequence K M).f 1

private theorem connecting_injective (M : AddCommGrpCat.{u}) :
    Function.Injective (connecting K M) := by
  obtain ⟨-, -, hExact, -, -⟩ := compactSupportFiveTerm K M
  have hZero := (compactSupportHZero_subsingleton K M).2
  intro x y h
  have hx : connecting K M (x - y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨a, ha⟩ := (hExact (x - y)).mp hx
  have ha0 : a = 0 := hZero.allEq _ _
  apply sub_eq_zero.mp
  rw [← ha, ha0, map_zero]

private def connectingToKernel (M : AddCommGrpCat.{u}) :
    boundarySections K M →+ (firstComparison K M).ker where
  toFun x := ⟨connecting K M x, by
    obtain ⟨-, -, -, hExact, -⟩ := compactSupportFiveTerm K M
    exact (hExact (connecting K M x)).mpr ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero (connecting K M))
  map_add' x y := Subtype.ext (map_add (connecting K M) x y)

/-- The actual kernel of the degree-one comparison is the origin coefficient group. -/
def firstKernelEquivOrigin (M : AddCommGrpCat.{u}) :
    (firstComparison K M).ker ≃+ M := by
  let f := connectingToKernel K M
  have hf : Function.Injective f :=
    fun x y h => connecting_injective K M (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨-, -, -, hExact, -⟩ := compactSupportFiveTerm K M
    obtain ⟨x, hx⟩ := (hExact y.val).mp y.property
    exact ⟨x, Subtype.ext hx⟩
  exact (AddEquiv.ofBijective f ⟨hf, hs⟩).symm.trans
    (compactSupportBoundaryHZeroEquiv K M)

/-- The extra term has exactly one copy of the cyclic order-ℓ coefficient. -/
theorem firstKernel_card (ℓ : ℕ) [Fact ℓ.Prime] :
    Nat.card (firstComparison K (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))).ker = ℓ := by
  let e := firstKernelEquivOrigin K (AddCommGrpCat.of (ULift.{u} (ZMod ℓ)))
  exact (Nat.card_congr (e.toEquiv.trans Equiv.ulift)).trans (by rw [Nat.card_eq_fintype_card, ZMod.card])

end

end ManuscriptAudit.CuspCompactSupportExcess

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportExcess.firstKernelEquivOrigin,
      ``ManuscriptAudit.CuspCompactSupportExcess.firstKernel_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
