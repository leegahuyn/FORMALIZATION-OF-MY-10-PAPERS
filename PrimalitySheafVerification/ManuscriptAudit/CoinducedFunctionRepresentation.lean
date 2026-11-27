import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Right-translation functions are coinduced from the trivial subgroup

The genuine coinduction from the trivial subgroup has all functions
as its underlying space. This identifies the right-translation
representation as acyclic in positive degrees.
-/

namespace ManuscriptAudit.CoinducedFunctionRepresentation

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]

/-- The representation on all functions, acting by right translation. -/
def functions : Rep.{u} k G :=
  Rep.of
    { toFun := fun g ↦
        { toFun := fun f : G → M ↦ fun x ↦ f (x * g)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      map_one' := by
        apply LinearMap.ext
        intro f
        funext x
        change f (x * 1) = f x
        rw [mul_one]
      map_mul' := fun g h ↦ by
        apply LinearMap.ext
        intro f
        funext x
        change f (x * (g * h)) = f ((x * g) * h)
        rw [mul_assoc] }

@[simp] theorem functions_apply (g x : G) (f : G → M) :
    ((functions k G M).ρ g f) x = f (x * g) := rfl

private abbrev B := (⊥ : Subgroup G)

private abbrev trivialRep := Rep.trivial k (B G) M

private abbrev coindBot := Rep.coind (B G).subtype (trivialRep k G M)

private def coindBotEquiv : (coindBot k G M).V ≃ₗ[k] (G → M) where
  toFun := Subtype.val
  invFun f := ⟨f, fun g x ↦ by
    have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
    change f ((g : G) * x) = f x
    rw [hg, one_mul]⟩
  left_inv f := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The right-translation representation is the actual coinduction
of the trivial action of the trivial subgroup. -/
def coindBotIsoFunctions :
    coindBot k G M ≅ functions k G M :=
  Rep.mkIso <| .mk (coindBotEquiv k G M) (fun _ ↦ LinearMap.ext fun _ ↦ rfl)

/-- Right-translation functions have vanishing positive group cohomology. -/
theorem functions_H_succ_isZero (n : ℕ) :
    IsZero (groupCohomology (functions k G M) (n + 1)) := by
  letI : Subsingleton ↥(B G) :=
    ⟨fun x y ↦ Subtype.ext ((Subgroup.mem_bot.mp x.property).trans
      (Subgroup.mem_bot.mp y.property).symm)⟩
  let e := ((groupCohomology.functor k G (n + 1)).mapIso (coindBotIsoFunctions k G M)).symm ≪≫
    groupCohomology.coindIso (trivialRep k G M) (n + 1)
  exact (isZero_groupCohomology_succ_of_subsingleton
    (trivialRep k G M) n).of_iso e

theorem functions_H_succ_subsingleton (n : ℕ) :
    Subsingleton (groupCohomology (functions k G M) (n + 1)) :=
  ModuleCat.subsingleton_of_isZero (functions_H_succ_isZero k G M n)

variable {k G} in
/-- Every representation embeds in the right-translation functions
with values in its underlying module. -/
def embedding (A : Rep.{u} k G) : A ⟶ functions k G A.V :=
  Rep.ofHom
    { toFun := fun a x ↦ A.ρ x a
      map_add' := fun a b ↦ funext fun x ↦ (A.ρ x).map_add a b
      map_smul' := fun c a ↦ funext fun x ↦ (A.ρ x).map_smul c a
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro a
        funext x
        change A.ρ x (A.ρ g a) = A.ρ (x * g) a
        rw [map_mul] <;> rfl }

variable {k G} in
/-- Evaluation at the identity detects equality of embedded elements. -/
theorem embedding_injective (A : Rep.{u} k G) :
    Function.Injective (embedding A).hom := by
  intro a b hab
  have h := congrArg (fun f : G → A.V ↦ f 1) hab
  change A.ρ 1 a = A.ρ 1 b at h
  rw [map_one] at h
  exact h

end

end ManuscriptAudit.CoinducedFunctionRepresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoinducedFunctionRepresentation.coindBotIsoFunctions,
      ``ManuscriptAudit.CoinducedFunctionRepresentation.functions_H_succ_subsingleton,
      ``ManuscriptAudit.CoinducedFunctionRepresentation.embedding_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
