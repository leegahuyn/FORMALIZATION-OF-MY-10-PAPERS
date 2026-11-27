import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAllHigher
import PrimalitySheafVerification.ManuscriptAudit.CuspHTwoCyclic

/-! Compactly supported cohomology of the actual affine cusp and its puncture for every invertible cyclic order. -/

namespace ManuscriptAudit.CuspCompactSupportCyclicDegrees

open CategoryTheory CuspCompactSupportSequence

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [kClosed : IsAlgClosed K]
variable (p : ℕ) [pPrime : Fact p.Prime] [pChar : CharP K p]
variable (d : ℕ) [dNZ : NeZero (d : K)]

private abbrev coeff := AddCommGrpCat.of (ZMod d)

private def trivialEquiv {A : Type} [AddCommGroup A] (h : Subsingleton A) : A ≃+ ZMod 1 where
  toFun := fun _ ↦ 0
  invFun := fun _ ↦ 0
  left_inv := fun x ↦ h.elim 0 x
  right_inv := fun x ↦ Subsingleton.elim 0 x
  map_add' := fun _ _ ↦ by rw [zero_add]

include kClosed p pPrime pChar dNZ

/-- An additive identification of the native degree-two cusp group for any invertible cyclic order. -/
def cuspTwoEquiv (hd : 2 ≤ d) : cuspHc K (coeff d) 2 ≃+ ZMod d :=
  Classical.choice (CuspCompactSupportDegreeTwo.nonempty_cuspHcTwoEquiv K p d hd)

/-- Use the same degree-two generator on the puncture via the actual open extension map. -/
def punctureTwoEquiv (hd : 2 ≤ d) : punctureHc K (coeff d) 2 ≃+ ZMod d :=
  (compactSupportHigherEquiv K (coeff d) 0).trans (cuspTwoEquiv K p d hd)

theorem punctureTwoEquiv_apply (hd : 2 ≤ d) (x : punctureHc K (coeff d) 2) :
    punctureTwoEquiv K p d hd x =
      cuspTwoEquiv K p d hd (Sheaf.H.map (compactSupportSequence K (coeff d)).f 2 x) :=
  rfl

/-- The actual affine cusp has one cyclic compactly supported group in degree two. -/
def cuspEquiv (hd : 2 ≤ d) (n : ℕ) :
    cuspHc K (coeff d) n ≃+ ZMod (if n = 2 then d else 1) := by
  cases n with
  | zero =>
    change cuspHc K (coeff d) 0 ≃+ ZMod 1
    exact trivialEquiv (compactSupportHZero_subsingleton K (coeff d)).2
  | succ n =>
    cases n with
    | zero =>
      change cuspHc K (coeff d) 1 ≃+ ZMod 1
      exact trivialEquiv (CuspCompactSupportAbsoluteHOne.cuspHcOne_subsingleton K p d)
    | succ n =>
      cases n with
      | zero =>
        change cuspHc K (coeff d) 2 ≃+ ZMod d
        exact cuspTwoEquiv K p d hd
      | succ n =>
        change cuspHc K (coeff d) (n + 3) ≃+ ZMod (if n + 3 = 2 then d else 1)
        rw [if_neg (by omega : n + 3 ≠ 2)]
        exact trivialEquiv (CuspCompactSupportAllHigher.cuspHc_add_three_subsingleton K p d n)

/-- The actual puncture has one cyclic compactly supported group in each of degrees one and two. -/
def punctureEquiv (hd : 2 ≤ d) (n : ℕ) :
    punctureHc K (coeff d) n ≃+ ZMod (if n = 1 ∨ n = 2 then d else 1) := by
  cases n with
  | zero =>
    change punctureHc K (coeff d) 0 ≃+ ZMod 1
    exact trivialEquiv (compactSupportHZero_subsingleton K (coeff d)).1
  | succ n =>
    cases n with
    | zero =>
      change punctureHc K (coeff d) 1 ≃+ ZMod d
      exact CuspCompactSupportAbsoluteHOne.punctureHcOneEquiv K p d
    | succ n =>
      cases n with
      | zero =>
        change punctureHc K (coeff d) 2 ≃+ ZMod d
        exact punctureTwoEquiv K p d hd
      | succ n =>
        change punctureHc K (coeff d) (n + 3) ≃+
          ZMod (if n + 3 = 1 ∨ n + 3 = 2 then d else 1)
        rw [if_neg (by omega : ¬ (n + 3 = 1 ∨ n + 3 = 2))]
        exact trivialEquiv (CuspCompactSupportAllHigher.punctureHc_add_three_subsingleton K p d n)

end
end ManuscriptAudit.CuspCompactSupportCyclicDegrees

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspCompactSupportCyclicDegrees.cuspTwoEquiv,
      ``ManuscriptAudit.CuspCompactSupportCyclicDegrees.punctureTwoEquiv,
      ``ManuscriptAudit.CuspCompactSupportCyclicDegrees.punctureTwoEquiv_apply,
      ``ManuscriptAudit.CuspCompactSupportCyclicDegrees.cuspEquiv,
      ``ManuscriptAudit.CuspCompactSupportCyclicDegrees.punctureEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
