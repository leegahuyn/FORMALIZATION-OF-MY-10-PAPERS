import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSequence

/-! The native Kummer sequence reduces cyclic degree-one vanishing to
divisibility of global units and torsion-freeness of native Pic. -/

namespace ManuscriptAudit.ProetaleKummerTorsionFree

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleUnitSheaf (unitSheaf)
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (sequence sequence_shortExact constantKernelIso)
open ProetaleKummerCoefficientMap (coefficientGroup)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

theorem map_power_apply (d n : ℕ) (a : Sheaf.H (unitSheaf X) n) :
    Sheaf.H.map (power X d) n a = d • a := by
  change Sheaf.H.map (d • 𝟙 (unitSheaf X)) n a = d • a
  induction d with
  | zero => simp [Sheaf.H.map_apply]
  | succ d ih =>
    change Sheaf.H.map ((d + 1) • 𝟙 (unitSheaf X)) n a = (d + 1) • a
    simp only [add_nsmul, one_nsmul, Sheaf.H.map_add_apply, Sheaf.H.map_id_apply]
    exact congrArg (fun x : Sheaf.H (unitSheaf X) n ↦ x + a) ih

variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))
  (d : ℕ) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

include k in
/-- Native degree-one root cohomology vanishes if coordinate powers
are surjective in degree zero and the unit group in degree one has
no nonzero d-torsion. -/
theorem roots_HOne_subsingleton
    (hZero : Function.Surjective (fun a : Sheaf.H (unitSheaf X) 0 ↦ d • a))
    (hOne : ∀ a : Sheaf.H (unitSheaf X) 1, d • a = 0 → a = 0) :
    Subsingleton (Sheaf.H ((constantSheaf (J X) G).obj (coefficientGroup K d)) 1) := by
  let Z := (constantSheaf (J X) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))
  let h := sequence_shortExact k d
  let δ : Sheaf.H (unitSheaf X) 0 →+ Sheaf.H (kernel (power X d)) 1 :=
    h.extClass.postcomp Z (show 0 + 1 = 1 by rfl)
  have he₀ := Ext.covariant_sequence_exact₃' Z h 0 1 rfl
  have he₁ := Ext.covariant_sequence_exact₁' Z h 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at he₀ he₁
  have ex₀ : Function.Exact (Sheaf.H.map (power X d) 0) δ := he₀
  have ex₁ : Function.Exact δ (Sheaf.H.map (kernel.ι (power X d)) 1) := he₁
  let r := ProetaleCohomologyIso.cohomologyIso (X := X) (constantKernelIso k d) 1
  refine subsingleton_of_forall_eq 0 (fun a ↦ ?_)
  have hz : Sheaf.H.map (kernel.ι (power X d)) 1 (r a) = 0 := by
    apply hOne
    rw [← map_power_apply X d 1, ← Sheaf.H.map_comp_apply, kernel.condition]
    simp [Sheaf.H.map_apply]
  obtain ⟨b, hb⟩ := (ex₁ (r a)).mp hz
  obtain ⟨c, hc⟩ := hZero b
  have hδ : δ b = 0 := (ex₀ b).mpr ⟨c, (map_power_apply X d 0 c).trans hc⟩
  apply r.injective
  rw [map_zero, ← hb, hδ]

end
end ManuscriptAudit.ProetaleKummerTorsionFree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerTorsionFree.map_power_apply,
      ``ManuscriptAudit.ProetaleKummerTorsionFree.roots_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
