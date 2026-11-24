import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Roots of unity as locally constant sections

Over an algebraically closed field where the degree is invertible, an affine
section of the root-of-unity kernel determines a locally constant root label
on the prime spectrum. This treatment allows disconnected affine objects.
-/

namespace ManuscriptAudit.KummerRootLabels

open scoped BigOperators Topology

noncomputable section

variable {A B K : Type*} [CommRing A] [CommRing B] [Field K]

/-- The image of a unit root of unity under a ring homomorphism. -/
def mapRoots (d : ℕ) (f : A →+* B) : rootsOfUnity d A →* rootsOfUnity d B :=
  MonoidHom.codRestrict ((Units.map f.toMonoidHom).comp (rootsOfUnity d A).subtype)
    (rootsOfUnity d B) fun a => map_rootsOfUnity (Units.map f.toMonoidHom) d
      ⟨a.1, a.2, rfl⟩

private abbrev rootValue {R : Type*} [CommRing R] {d : ℕ} (a : rootsOfUnity d R) : R :=
  ((a : Rˣ) : R)

variable [IsAlgClosed K] [Algebra K A] {d : ℕ} [NeZero d] [NeZero (d : K)]

private abbrev coefficientResidue (P : PrimeSpectrum A) : K →+* A ⧸ P.asIdeal :=
  (Ideal.Quotient.mk P.asIdeal).comp (algebraMap K A)

private theorem coefficientResidue_injective (P : PrimeSpectrum A) :
    Function.Injective (coefficientResidue (K := K) P) := by
  letI : IsDomain (A ⧸ P.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  exact RingHom.injective _

private theorem primitiveRoots_nonempty : (primitiveRoots d K).Nonempty := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K d
  exact ⟨ζ, (mem_primitiveRoots (NeZero.pos d)).mpr hζ⟩

private def rootTagHom (P : PrimeSpectrum A) : rootsOfUnity d A →* rootsOfUnity d K := by
  letI : IsDomain (A ⧸ P.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  exact (rootsOfUnityEquivOfPrimitiveRoots (coefficientResidue_injective (K := K) P)
    (primitiveRoots_nonempty (K := K) (d := d))).symm.toMonoidHom.comp
      (mapRoots d (Ideal.Quotient.mk P.asIdeal))

private def rootTag (a : rootsOfUnity d A) (P : PrimeSpectrum A) : rootsOfUnity d K :=
  rootTagHom P a

private theorem rootTag_residue (a : rootsOfUnity d A) (P : PrimeSpectrum A) :
    coefficientResidue P (rootValue (rootTag (K := K) a P)) =
      Ideal.Quotient.mk P.asIdeal (rootValue a) := by
  letI : IsDomain (A ⧸ P.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    (coefficientResidue_injective (K := K) P)
    (primitiveRoots_nonempty (K := K) (d := d))
    (mapRoots d (Ideal.Quotient.mk P.asIdeal) a)

private theorem rootTag_eq_iff (a : rootsOfUnity d A) (P : PrimeSpectrum A)
    (ζ : rootsOfUnity d K) :
    rootTag a P = ζ ↔ rootValue a - algebraMap K A (rootValue ζ) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq]
  constructor
  · intro h
    rw [← h]
    exact (rootTag_residue (K := K) a P).symm
  · intro h
    apply Subtype.ext
    apply Units.ext
    apply coefficientResidue_injective (K := K) P
    exact (rootTag_residue (K := K) a P).trans h

private theorem rootTag_fiber (a : rootsOfUnity d A) (ζ : rootsOfUnity d K) :
    rootTag a ⁻¹' {ζ} = PrimeSpectrum.zeroLocus {rootValue a - algebraMap K A (rootValue ζ)} := by
  ext P
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, PrimeSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff] using rootTag_eq_iff a P ζ

private theorem isLocallyConstant_rootTag (a : rootsOfUnity d A) :
    IsLocallyConstant (rootTag (K := K) a) := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro ζ
  have hcompl : (rootTag (K := K) a ⁻¹' {ζ})ᶜ =
      ⋃ η : {η : rootsOfUnity d K // η ≠ ζ}, rootTag a ⁻¹' {η.1} := by
    ext P
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨⟨rootTag a P, h⟩, rfl⟩
    · rintro ⟨η, h⟩ heq
      exact η.2 (h.symm.trans heq)
  rw [← isClosed_compl_iff, hcompl]
  apply isClosed_iUnion_of_finite
  intro η
  rw [rootTag_fiber]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- A root of unity determines its coefficient-root label at every prime.
The label is locally constant and multiplicative in the input. -/
def locallyConstantRootTag :
    rootsOfUnity d A →* LocallyConstant (PrimeSpectrum A) (rootsOfUnity d K) where
  toFun a := ⟨rootTag a, isLocallyConstant_rootTag a⟩
  map_one' := LocallyConstant.ext fun P => (rootTagHom P).map_one
  map_mul' a b := LocallyConstant.ext fun P => (rootTagHom P).map_mul a b

/-- Each coefficient-root fiber is the clopen defined by an idempotent. -/
theorem locallyConstantRootTag_idempotent (a : rootsOfUnity d A) (ζ : rootsOfUnity d K) :
    ∃ e : A, IsIdempotentElem e ∧
      {P | locallyConstantRootTag a P = ζ} = PrimeSpectrum.basicOpen e :=
  PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ((isLocallyConstant_rootTag a).isClopen_fiber ζ)

/-- The locally constant label is compatible with change of affine object. -/
theorem locallyConstantRootTag_natural [Algebra K B] (f : A →ₐ[K] B)
    (a : rootsOfUnity d A) (P : PrimeSpectrum B) :
    locallyConstantRootTag (mapRoots d f.toRingHom a) P =
      locallyConstantRootTag a (PrimeSpectrum.comap f.toRingHom P) := by
  change rootTag (K := K) (mapRoots d f.toRingHom a) P =
    rootTag (K := K) a (PrimeSpectrum.comap f.toRingHom P)
  apply (rootTag_eq_iff _ _ _).mpr
  let Q := PrimeSpectrum.comap f.toRingHom P
  have h := (rootTag_eq_iff a Q (rootTag (K := K) a Q)).mp rfl
  change f (rootValue a - algebraMap K A (rootValue (rootTag (K := K) a Q))) ∈ P.asIdeal at h
  rw [map_sub, f.commutes] at h
  exact h

/-- On a reduced algebra, the labels determine the original root of unity. -/
theorem locallyConstantRootTag_injective [IsReduced A] :
    Function.Injective (locallyConstantRootTag (K := K) (A := A) (d := d)) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  apply sub_eq_zero.mp
  apply IsNilpotent.eq_zero
  apply nilpotent_iff_mem_prime.mpr
  intro I hI
  let P : PrimeSpectrum A := ⟨I, hI⟩
  have heq : rootTag (K := K) a P = rootTag (K := K) b P :=
    DFunLike.congr_fun h P
  have ha := rootTag_residue (K := K) a P
  rw [heq] at ha
  exact Ideal.Quotient.eq.mp (ha.symm.trans (rootTag_residue (K := K) b P))

/-- Each locally constant coefficient-root label comes from a root of unity
on a reduced algebra. Clopen fibers supply its idempotent coordinates. -/
theorem locallyConstantRootTag_surjective [IsReduced A] :
    Function.Surjective (locallyConstantRootTag (K := K) (A := A) (d := d)) := by
  classical
  intro w
  letI := Fintype.ofFinite (rootsOfUnity d K)
  choose e he hFiber using fun ζ : rootsOfUnity d K =>
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
      (w.isLocallyConstant.isClopen_fiber ζ)
  let z : A := ∑ ζ : rootsOfUnity d K, e ζ * algebraMap K A (rootValue ζ)
  have hzres (P : PrimeSpectrum A) :
      Ideal.Quotient.mk P.asIdeal z = coefficientResidue P (rootValue (w P)) := by
    letI : IsDomain (A ⧸ P.asIdeal) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
    let q := Ideal.Quotient.mk P.asIdeal
    have heone : q (e (w P)) = 1 := by
      have hn : e (w P) ∉ P.asIdeal := by
        apply (PrimeSpectrum.mem_basicOpen _ _).mp
        change P ∈ (PrimeSpectrum.basicOpen (e (w P)) : Set (PrimeSpectrum A))
        rw [← hFiber]
        rfl
      rcases (IsIdempotentElem.iff_eq_zero_or_one).mp ((he (w P)).map q) with hzero | hone
      · exact (hn (Ideal.Quotient.eq_zero_iff_mem.mp hzero)).elim
      · exact hone
    have hezero (ζ : rootsOfUnity d K) (hζ : ζ ≠ w P) : q (e ζ) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      by_contra hn
      have hP := (PrimeSpectrum.mem_basicOpen (e ζ) P).mpr hn
      change P ∈ (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum A)) at hP
      rw [← hFiber] at hP
      exact hζ hP.symm
    change q (∑ ζ : rootsOfUnity d K, e ζ * algebraMap K A (rootValue ζ)) =
      q (algebraMap K A (rootValue (w P)))
    rw [map_sum]
    refine (Finset.sum_eq_single (w P) ?_ ?_).trans ?_
    · intro ζ _ hζ
      rw [map_mul, hezero ζ hζ, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
    · rw [map_mul, heone, one_mul]
  have hz : z ^ d = 1 := by
    apply sub_eq_zero.mp
    apply IsNilpotent.eq_zero
    apply nilpotent_iff_mem_prime.mpr
    intro I hI
    let P : PrimeSpectrum A := ⟨I, hI⟩
    have hpow : rootValue (w P) ^ d = 1 :=
      (mem_rootsOfUnity' d (w P : Kˣ)).mp (w P).prop
    apply Ideal.Quotient.eq.mp
    change Ideal.Quotient.mk P.asIdeal (z ^ d) = Ideal.Quotient.mk P.asIdeal 1
    rw [map_pow, hzres P, ← map_pow, hpow, map_one, map_one]
  refine ⟨rootsOfUnity.mkOfPowEq z hz, LocallyConstant.ext fun P => ?_⟩
  change rootTag (rootsOfUnity.mkOfPowEq z hz) P = w P
  apply (rootTag_eq_iff _ _ _).mpr
  exact Ideal.Quotient.eq.mp (hzres P)

/-- Roots of unity on a reduced affine algebra are exactly the locally
constant maps from its prime spectrum to coefficient roots. -/
def locallyConstantRootsEquiv [IsReduced A] :
    rootsOfUnity d A ≃* LocallyConstant (PrimeSpectrum A) (rootsOfUnity d K) :=
  MulEquiv.ofBijective locallyConstantRootTag
    ⟨locallyConstantRootTag_injective, locallyConstantRootTag_surjective⟩

end

end ManuscriptAudit.KummerRootLabels

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_idempotent,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_natural,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_injective,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_surjective,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootsEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
