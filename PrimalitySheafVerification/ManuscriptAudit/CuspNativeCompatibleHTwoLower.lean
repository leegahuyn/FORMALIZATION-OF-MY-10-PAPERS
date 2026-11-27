import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleConstantCohomologyNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentCompatibleHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisNaturality

/-! The proper cusp's actual finite pro-étale Mayer–Vietoris classes are
compatible under coefficient reduction and give an ordinary inverse-limit injection. -/

namespace ManuscriptAudit.CuspNativeCompatibleHTwoLower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspChartIntersection (overlapIsoLaurent)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open OpenProetaleExtension (restriction)
open ProetaleKummerCyclicCoordinates (cyclicGroup reduction)
open ProetaleConstantCohomologyNaturality (restrictionEquiv schemeEquiv
  restrictionEquiv_naturality schemeEquiv_naturality)
open ProetaleMayerVietorisConnecting (connecting connecting_injective)
open ProetaleMayerVietorisNaturality (connecting_naturality)
open CyclicPowerInverseLimit (compatibleTuples)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := overlapOpen K
private abbrev W := pullback (j K) (k K)

private abbrev F (Y : Scheme.{0}) (n : ℕ) :=
  (constantSheaf (Scheme.ProEt.topology Y) A).obj (cyclicGroup ℓ n)

private abbrev red (Y : Scheme.{0}) (n : ℕ) :=
  (constantSheaf (Scheme.ProEt.topology Y) A).map (reduction ℓ n)

local instance cast_pow_neZero (n : ℕ) : NeZero ((ℓ ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩

private def overlapEquiv (n : ℕ) :
    Sheaf.H ((restriction (l K) A).obj (F ℓ (X K) n)) 1 ≃+
      Sheaf.H (F ℓ (ProetaleLaurentCompatibleHOne.laurent K) n) 1 :=
  (restrictionEquiv (l K) (cyclicGroup ℓ n) 1).trans
    (schemeEquiv (overlapIsoLaurent K) (cyclicGroup ℓ n) 1)

set_option maxHeartbeats 1800000 in
private theorem overlap_naturality (n : ℕ)
    (x : Sheaf.H ((restriction (l K) A).obj (F ℓ (X K) (n + 1))) 1) :
    overlapEquiv K ℓ n (Sheaf.H.map ((restriction (l K) A).map (red ℓ (X K) n)) 1 x) =
      Sheaf.H.map (red ℓ (ProetaleLaurentCompatibleHOne.laurent K) n) 1 (overlapEquiv K ℓ (n + 1) x) := by
  let r := restrictionEquiv (l K) (cyclicGroup ℓ (n + 1)) 1
  let s := schemeEquiv (overlapIsoLaurent K) (cyclicGroup ℓ n) 1
  calc
    _ = s (Sheaf.H.map (red ℓ (W K) n) 1 (r x)) :=
      congrArg s (restrictionEquiv_naturality (l K) (reduction ℓ n) 1 x)
    _ = _ := schemeEquiv_naturality (overlapIsoLaurent K) (reduction ℓ n) 1 (r x)

/-- Actual native proper-cusp degree two with the indicated cyclic constants. -/
abbrev level (n : ℕ) := Sheaf.H (F ℓ (X K) n) 2

abbrev transition (n : ℕ) : level K ℓ (n + 1) →+ level K ℓ n :=
  Sheaf.H.map (red ℓ (X K) n) 2

private def overlapLabel (n : ℕ) :
    ZMod (ℓ ^ n) ≃+ Sheaf.H ((restriction (l K) A).obj (F ℓ (X K) n)) 1 :=
  (ProetaleLaurentCompatibleHOne.cyclicToHOne K ℓ n).trans (overlapEquiv K ℓ n).symm

/-- The actual Laurent Kummer exponent class maps into the proper cusp by native Mayer–Vietoris. -/
def cyclicInclusion (n : ℕ) : ZMod (ℓ ^ n) →+ level K ℓ n :=
  (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (F ℓ (X K) n) 1).comp (overlapLabel K ℓ n).toAddMonoidHom

theorem cyclicInclusion_injective (n : ℕ) : Function.Injective (cyclicInclusion K ℓ n) := by
  letI := CuspNativeProetaleAffineHOne.cyclic_HOne_subsingleton K (ℓ ^ n)
  letI := ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton K (ℓ ^ n)
  have hj := (restrictionEquiv (j K) (cyclicGroup ℓ n) 1).injective.subsingleton
  have hk := (restrictionEquiv (k K) (cyclicGroup ℓ n) 1).injective.subsingleton
  exact (connecting_injective (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (F ℓ (X K) n) 1 hj hk).comp (overlapLabel K ℓ n).injective

set_option maxHeartbeats 2000000 in
theorem cyclicInclusion_naturality (n : ℕ) (a : ZMod (ℓ ^ (n + 1))) :
    transition K ℓ n (cyclicInclusion K ℓ (n + 1) a) =
      cyclicInclusion K ℓ n (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a) := by
  let b := overlapLabel K ℓ (n + 1) a
  let c := overlapLabel K ℓ n (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a)
  have hb : overlapEquiv K ℓ (n + 1) b = ProetaleLaurentCompatibleHOne.cyclicToHOne K ℓ (n + 1) a :=
    (overlapEquiv K ℓ (n + 1)).apply_symm_apply _
  have hc : overlapEquiv K ℓ n c = ProetaleLaurentCompatibleHOne.cyclicToHOne K ℓ n
      (PadicResidueSystems.reduction ℓ (Nat.le_succ n) a) := (overlapEquiv K ℓ n).apply_symm_apply _
  have h : Sheaf.H.map ((restriction (l K) A).map (red ℓ (X K) n)) 1 b = c := by
    apply (overlapEquiv K ℓ n).injective
    rw [overlap_naturality, hb, hc]
    exact ProetaleLaurentCompatibleHOne.cyclicToHOne_naturality K ℓ n a
  let f := connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F ℓ (X K) n) 1
  exact (connecting_naturality (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
    (red ℓ (X K) n) 1 b).symm.trans (congrArg f h)

/-- The ordinary inverse limit of actual finite native degree-two classes contains a copy of the adic integers. -/
def inverseLimitInclusion : ℤ_[ℓ] →+ compatibleTuples (level K ℓ) (transition K ℓ) where
  toFun a := ⟨fun n ↦ cyclicInclusion K ℓ n (PadicInt.toZModPow n a), fun n ↦ by
    rw [cyclicInclusion_naturality]
    exact congrArg (cyclicInclusion K ℓ n)
      ((PadicResidueSystems.toSystems ℓ a).property n (n + 1) (Nat.le_succ n))⟩
  map_zero' := Subtype.ext (funext fun n ↦ by simp)
  map_add' a b := Subtype.ext (funext fun n ↦ by simp)

theorem inverseLimitInclusion_injective : Function.Injective (inverseLimitInclusion K ℓ) := by
  intro a b h
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact cyclicInclusion_injective K ℓ n (congrArg (fun s ↦ s.val n) h)

end
end ManuscriptAudit.CuspNativeCompatibleHTwoLower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompatibleHTwoLower.cyclicInclusion_injective,
      ``ManuscriptAudit.CuspNativeCompatibleHTwoLower.cyclicInclusion_naturality,
      ``ManuscriptAudit.CuspNativeCompatibleHTwoLower.inverseLimitInclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
