import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.ProetalePadicSectionTower
import PrimalitySheafVerification.ManuscriptAudit.StoneCechHOne

/-! Finite Stone-space Čech primitives can be chosen compatibly at every
residue level, giving a continuous primitive for an integral adic cocycle. -/

namespace ManuscriptAudit.StoneAdicCechHOne

open Topology
open StoneCechClopenBlocks (PairOver)
open ProetalePadicSectionTower (sectionTransition compatibleSections continuousSectionsEquiv)
open PadicResidueSystems (reduction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace Y] [T2Space X]
  (p : C(Y,X)) (hp : Function.Surjective p)
  (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

include hp in
private theorem exists_descended {M : Type} [TopologicalSpace M] (a : C(Y,M))
    (ha : ∀ x y, p x = p y → a x = a y) :
    ∃ b : C(X,M), ∀ y, b (p y) = a y := by
  classical
  have hs₀ := hp
  choose s hs using hs₀
  let b : X → M := fun x ↦ a (s x)
  have h (y : Y) : b (p y) = a y := ha (s (p y)) y (hs (p y))
  have hq : IsQuotientMap p := IsQuotientMap.of_surjective_continuous hp p.continuous
  have hC : Continuous b := hq.continuous_iff.mpr (by
    have he : b ∘ p = a := funext h
    rw [he]
    exact a.continuous)
  exact ⟨⟨b, hC⟩, h⟩

private abbrev redCocycle (b : C(PairOver p, ℤ_[ℓ])) (n : ℕ) :
    C(PairOver p, ZMod (ℓ ^ n)) :=
  ((continuousSectionsEquiv ℓ (PairOver p)) b).val n

private abbrev Sol (b : C(PairOver p, ℤ_[ℓ])) (n : ℕ) :=
  {a : C(Y, ZMod (ℓ ^ n)) //
    ∀ x y (e : p x = p y), a y - a x = redCocycle p ℓ b n ⟨(x,y),e⟩}

private theorem transition_sol (b : C(PairOver p, ℤ_[ℓ])) (n : ℕ)
    (a : Sol p ℓ b (n+1)) :
    ∀ x y (e : p x = p y),
      sectionTransition ℓ Y n a.val y - sectionTransition ℓ Y n a.val x =
        redCocycle p ℓ b n ⟨(x,y),e⟩ := by
  intro x y e
  let ρ := reduction ℓ (Nat.le_succ n)
  change ρ (a.val y) - ρ (a.val x) = _
  rw [← map_sub, a.property x y e]
  exact congrArg (fun f : C(PairOver p, ZMod (ℓ ^ n)) ↦ f ⟨(x,y),e⟩)
    (((continuousSectionsEquiv ℓ (PairOver p)) b).property n)

include hp in
set_option maxHeartbeats 2000000 in
private theorem lift_primitive (b : C(PairOver p, ℤ_[ℓ])) (n : ℕ)
    (a : Sol p ℓ b n) (b₀ : Sol p ℓ b (n+1)) :
    ∃ a' : Sol p ℓ b (n+1), sectionTransition ℓ Y n a'.val = a.val := by
  let t := sectionTransition ℓ Y n b₀.val
  let δ := a.val - t
  have hδ (x y : Y) (e : p x = p y) : δ x = δ y := by
    apply sub_eq_zero.mp
    calc
      δ x - δ y = (t y - t x) - (a.val y - a.val x) := by
        change (a.val x - t x) - (a.val y - t y) = _
        abel
      _ = 0 := by rw [transition_sol p ℓ b n b₀ x y e, a.property x y e, sub_self]
  obtain ⟨d, hd⟩ := exists_descended p hp δ hδ
  let ρ := reduction ℓ (Nat.le_succ n)
  choose s hs using (show Function.Surjective ρ from ZMod.ringHom_surjective ρ)
  let d' : C(X,ZMod (ℓ ^ (n+1))) :=
    ⟨fun x ↦ s (d x), continuous_of_discreteTopology.comp d.continuous⟩
  let a' : C(Y,ZMod (ℓ ^ (n+1))) := b₀.val + d'.comp p
  have ha' (x y : Y) (e : p x = p y) :
      a' y - a' x = redCocycle p ℓ b (n+1) ⟨(x,y),e⟩ := by
    change (b₀.val y + d' (p y)) - (b₀.val x + d' (p x)) = _
    rw [congrArg d' e.symm, ← b₀.property x y e]
    abel
  refine ⟨⟨a',ha'⟩, ContinuousMap.ext fun y ↦ ?_⟩
  change ρ (b₀.val y + d' (p y)) = a.val y
  rw [map_add]
  have he : ρ (d' (p y)) = d (p y) := hs (d (p y))
  rw [he, hd y]
  change t y + (a.val y - t y) = a.val y
  abel

variable [CompactSpace X] [T2Space Y] [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]

include hp in
set_option maxHeartbeats 2200000 in
/-- A continuous integral adic cocycle on the actual fibre-pair space
is a coboundary for every surjection of compact Stone spaces. -/
theorem exists_primitive (b : C(PairOver p, ℤ_[ℓ]))
    (hb : ∀ x y z (h₁ : p x = p y) (h₂ : p y = p z),
      b ⟨(x,y),h₁⟩ + b ⟨(y,z),h₂⟩ = b ⟨(x,z),h₁.trans h₂⟩) :
    ∃ a : C(Y,ℤ_[ℓ]), ∀ x y (e : p x = p y), a y - a x = b ⟨(x,y),e⟩ := by
  classical
  have hLevel (n : ℕ) : Nonempty (Sol p ℓ b n) := by
    letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime ℓ).ne_zero⟩
    have hc (x y z : Y) (h₁ : p x = p y) (h₂ : p y = p z) :
        redCocycle p ℓ b n ⟨(x,y),h₁⟩ + redCocycle p ℓ b n ⟨(y,z),h₂⟩ =
          redCocycle p ℓ b n ⟨(x,z),h₁.trans h₂⟩ := by
      let ρ : ℤ_[ℓ] →+* ZMod (ℓ ^ n) := PadicInt.toZModPow n
      change ρ (b ⟨(x,y),h₁⟩) + ρ (b ⟨(y,z),h₂⟩) = ρ (b ⟨(x,z),h₁.trans h₂⟩)
      rw [← map_add, hb x y z h₁ h₂]
    obtain ⟨a, ha⟩ := StoneCechHOne.exists_primitive p (redCocycle p ℓ b n) hc
    exact ⟨⟨a,ha⟩⟩
  have hStep (n : ℕ) (a : Sol p ℓ b n) :
      ∃ a' : Sol p ℓ b (n+1), sectionTransition ℓ Y n a'.val = a.val :=
    lift_primitive p hp ℓ b n a (Classical.choice (hLevel (n+1)))
  choose step hstep using hStep
  let f : (n : ℕ) → Sol p ℓ b n := Nat.rec (Classical.choice (hLevel 0)) step
  let g : compatibleSections ℓ Y :=
    ⟨fun n ↦ (f n).val, fun n ↦ hstep n (f n)⟩
  let e := continuousSectionsEquiv ℓ Y
  let a := e.symm g
  have ha (n : ℕ) (y : Y) : PadicInt.toZModPow n (a y) = (f n).val y :=
    congrArg (fun v : compatibleSections ℓ Y ↦ v.val n y) (e.apply_symm_apply g)
  refine ⟨a, fun x y hxy ↦ PadicInt.ext_of_toZModPow.mp fun n ↦ ?_⟩
  change PadicInt.toZModPow n (a y - a x) = PadicInt.toZModPow n (b ⟨(x,y),hxy⟩)
  rw [map_sub, ha n y, ha n x]
  exact (f n).property x y hxy

end
end ManuscriptAudit.StoneAdicCechHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.StoneAdicCechHOne.exists_primitive
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
