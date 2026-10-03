# QYM part 2 (lines 15736–31400) — 진행 노트 (중간 저장)

## 진행 메모 (Read 15736–22385)
- 15736-15786 ComplexRootExponentialExtension 끝: finite-modification invariance (C 확대 허용). 소규모 진짜 증명.
- 15801-15920 PaperNormalized Thm 4.26 complex 래퍼: 정직(“Rademacher main term / mock coefficient estimate 미확립” 명시). 조건부(C) + 고정상수 반례.
- 15935-16165 TruncationGapStabilityCore: UniformEigenvalueError → gap 오차 2r (linarith), quarter→half gap, moving-index spike (pointwise≠uniform). 초등적, 정확.
- 16177-16296 PaperNormalized Hyp 4.24/Cor 4.25/Prop 4.23 “calibrated truncation”: 가설(균일 고유값오차+보정곱) ⇒ 결론, 1-2줄 linarith. (C, 가설이 핵심 내용을 운반)
- 16307-16501 TypedEvidenceAnalyticBridgeExtension (11 tags): 순수 스캐폴딩.
- 16518-16975 UnboundedLinearPMapExtension: Mathlib LinearPMap(closure, adjoint, IsSelfAdjoint) 얇은 래퍼. zeroBottomOperator (⊥ domain) 반례: symmetric but not dense/not self-adjoint. 정확.
- 16991-17173 PaperNormalized Lemma 4.13/4.16 LinearPMap boundary: Mathlib 정리 재포장(U, 얇음). docstring 정직("q-YM form 미구성").
- 17193-17499 LaxMilgramFormExtension: Mathlib IsCoercive/continuousLinearEquivOfBilin 래퍼 + 명시상수 a-priori ‖u‖≤‖f‖/c, 대각 섭동 c-δ. (U, 얇음, 정확)
- 17516-17627 PaperNormalized bounded Lax–Milgram (U). docstring: "bounded only; Friedrichs/compact resolvent 아님" 정직.
- 17643-17950 CompactResolventLogicExtension: 1차 resolvent 항등식(noncomm), resolvent compactness 점 이동, **bounded T의 compact resolvent ⇒ finite-dim** (FiniteDimensional.of_isCompactOperator_id) — 유계 대리모델 불가 no-go (정확·유용). coercive sublevel + compact embedding ⇒ precompact; norm² 단위구 비컴팩트.
- 17965-18100 PaperNormalized 위 래퍼(U).
- 18113-18329 TypedEvidenceUnboundedFormResolventExtension (12 tags): 스캐폴딩.
- 18355-18822 FormDomainRealizationExtension: bounded form B, dense injective j로 실제 LinearPMap 구성(Represents, formDomain, Classical.choose는 존재 증명 후 유일 대표 선택 — 정당), symmetric/nonneg 이전, dense ⇒ closable, self-adjoint ↔ A†≤A. 진짜 구성(U).
- 18843-18956 PaperNormalized (U).
- 18971-19424 UnboundedResolventDataExtension: ResolventData 구조(inverse, mapsToDomain, left/right inverse) — Prop 필드는 결론이 아닌 정의적 역 방정식: SUBSTANTIVE(정의). ⇒ closed, 1차 resolvent 항등식, compact transfer; no-go: compact resolvent ⇒ bounded shift 불가(무한차원). bottom domain ⇒ resolvent 없음. 정확.
- 19439-19598 PaperNormalized (U).
- 19626-20146 CompactSelfAdjointGapExtension: Mathlib compact s.a. spectral thm 래퍼, nonzero eigenspace 유한차원, **HasGroundComplementCoercivity T c ⇒ 모든 nonzero 고유값 ≥ c** (Rayleigh 1줄; 가설이 사실상 gap 자체 — NEAR-CIRCULAR), 유한차원 first positive eigenvalue (Finset.min') 구성(진짜), lower_bounds_alone_do_not_force_gap (2,0,3,4 산술 반례: 논문 Prop 4.23/A.7 추론 오류 지적), compact+norm lower bound ⇒ finite-dim, 1D scalar 반례. AwayFromZeroPointSpectrumFinite 구조(SUBSTANTIVE, 참인 Riesz–Schauder 사실).
- 20169-20359 PaperNormalized prop4_23/theoremA_7 "corrected" = 위 정리 별칭. **theoremA_7_groundComplementCoerciveGapStatement := prop4_23_...** — 질량간극 "정리"는 유계 T + 가정된 ground-complement coercivity ⇒ 고유값 ≥ c. 실제 q-YM Hamiltonian과 무관.
- 20376-20691 TypedEvidenceFormResolventSpectralExtension (24 tags): 스캐폴딩.
- 20718-21398 CoerciveFormFriedrichsExtension: **진짜 실질 수학** — Gårding bound(IsPositiveCoerciveShift) 하에서 Lax–Milgram로 (A+μ)^{-1}=j∘C^{-1}∘j† 구성, 도메인 dense (j† dense range from injectivity), 표면 surjectivity ⇒ A†≤A ⇒ self-adjoint (최대대칭성 논증 직접 증명), resolvent data at -μ, j compact ⇒ compact resolvent. Friedrichs/first representation theorem의 실 Hilbert, bounded-form-on-V 버전. Mathlib PR 후보.
- 21410-21531 PaperNormalized (U, 조건: Gårding + compact j).
- 21543-21662 TypedEvidenceCoerciveFriedrichsExtension (4 tags) 스캐폴딩.
- 21679-21867 BoundedSelfAdjointPMapPerturbationExtension: self-adjoint LinearPMap + bounded symmetric ⇒ self-adjoint (adjoint domain 논증 직접 증명; 진짜, upstream 후보), lower bound c-‖B‖.
- 21878-21930 PaperNormalized Lemma 4.30 B1 (U).
- 21964-22385 FormSmallOperatorPerturbationExtension: KLMN 유사 (|E(u,u)| ≤ a C(u,u)+b‖ju‖², a<1) ⇒ 잔여 coercivity (1-a)c ⇒ Friedrichs 구성 재사용 ⇒ self-adjoint, resolvent, compact. (U, 단 E는 V 위 bounded form)

## 진행 메모 (Read 22386–27385)
- 22386-22543 FormSmall 끝: direct-residual route; a=1 scalar cancellation 반례 (zero base form + -⟨x,y⟩) — 임계값 필요성 (정확, 1D toy).
- 22561-22800 PaperNormalized Def 4.8/Lemma 4.30/Thm 4.31/Cor 4.32 "B2 component/prerequisite": def4_8_… := rfl (T, 정의 재진술). 나머지 U(조건: Gårding+relative bound+compact j). docstring "statement-level 동치 아님, min-max 별도" 정직.
- 22826-24005 RCLikeCoerciveFormFriedrichsExtension: 복소(RCLike) 버전 — 실수 Lax–Milgram을 realification 후 v, I•v 테스트로 복소 방정식 복원 (eq_of_re_eq_of_re_I_mul_eq), 𝕜-선형성은 변분 유일성으로 증명. 이후 실수판(20718-21398)과 거의 동일한 ~700줄 복제 (positiveShift, maximal symmetry, resolvent data, compact). 진짜 수학이지만 중복. local instance rclikeToReal 4개 (22836-22845) — 국소적, 안전.
- 24022-24179 PaperNormalized RCLike "prerequisite" (U, 조건부). docstring: "Prop 4.23 mass-gap lower bound 주장 안 함" 정직.
- 24209-24780 UnboundedCompactSpectralMappingExtension: LinearPMap 고유공간 = resolvent 고유공간 ((z-λ)^{-1}) 부분모듈 등식 (진짜), finite multiplicity, real-z resolvent 자기수반, 고유공간 완비성 이전, HasGroundComplementCoercivity (LinearPMap판) ⇒ 0≠λ≥c, PositivePointSpectrumLocallyFinite ⇒ least positive eigenvalue (Set.exists_min_image), exists_multiplicitySafe_least_offGround_level (hAway 공급자 사용).
- 24810-25035 PaperNormalized prop4_23 prerequisite / theoremA_7_unboundedMultiplicitySafeLeastGapStatement (hAway + coercivity 가정) / cor4_25 uniform. docstring에 "prop4_23_ 접두는 prerequisite bridge, mass-gap 결론 아님" 명시.
- 25057-25368 CompactSelfAdjointAwayFromZeroExtension: **AwayFromZeroPointSpectrumFinite DISCHARGED** — ε-분리 집합 유한성(totally bounded 덮개 중심 단사), 단위 고유벡터 정규화, 직교 ⇒ 이미지 거리 ≥ r (Pythagoras), compact image ⇒ 유한. awayFromZeroPointSpectrumFinite_of_compact_symmetric (L25349). 진짜 실질 증명, Mathlib PR 후보 (Mathlib에 없다는 주장은 FredholmAlternative 언급과 함께 그럴듯하나 미검증).
- 25372-25436 hAway 제거판: exists_multiplicitySafe_least_offGround_level_of_compact_negative_resolvent — docstring "Unconditional standard functional-analysis form" (단, HasGroundComplementCoercivity T c 가설 여전히 존재).
- 25451-25582 PaperNormalized WithoutSupplier 판 (theoremA_7_…WithoutSupplierStatement, cor4_25_…WithoutSupplier).
- 25600-25994 TypedEvidenceUnconditionalFunctionalAnalysisExtension (29 tags): 스캐폴딩; 이름의 "Unconditional"은 추상 FA 정리라는 의미일 뿐 q-YM 무조건이 아님 (docstring은 "narrow associations, not equivalence" 명시). hypA_6_has_no_evidence := rfl.
- 26029-26385 ClosedOperatorEnergyFormExtension: graph-norm form domain (D.graph 부분타입), energyForm = ⟨Dx,Dy⟩ sesquilinear, closed form ⟺ D closed, Cauchy 좌표 극한. 진짜지만 얇음. docstring: δ_q LinearPMap의 closed/dense는 "honest paper-specific suppliers"로 명시.
- 26414-26806 CompactResolventPureDiscreteExtension: **HilbertBasis.mkOfOrthogonalEqBot로 비가산 가능 index 고유기저 구성** (진짜), point spectrum 유계구 유한·가산, finite-fiber 고유값열 → ∞.
- 26835-27069 CompactResolventLowLyingGapExtension: MultiplicitySafeGapWitness (Prop 구조, 결론 묶음; 구성됨). adjacent index: eigenvalue 1 ≠ 0 가정 시 c ≤ λ1-λ0. firstOffGroundIndex (Nat.find). **exists_gapFamily_with_positive_ennreal_liminf: 균일 coercivity c 가정 ⇒ gap Y ≥ c ⇒ liminf>0** — 균일성이 바로 가정(질량간극의 실제 난점)이므로 정량부 NEAR-CIRCULAR; docstring "corrected unconditional functional-analysis form"은 과장.
- 27093-27333 PaperNormalized Lemma 4.13/4.18/A.7/Cor 4.25 component 래퍼 (U 조건부).

## 이어서 (27386–31400)

(후속 범위 감사자 작성. 27386–31405를 원본 `.lean`에서 순차 정독함 — 생략 없음. 27345–27385는 이전 감사자 범위였던 `TypedEvidenceClosedPureDiscreteGapExtension` 서두.)

### 진행 메모 (Read 27386–31405)
- 27386-27530 `TypedEvidenceClosedPureDiscreteGapExtension` 후반: `evidenceSound`(11 tags → PaperNormalized 정리 재호출), `Certificate {id; proof}`, `allEvidence_length = 11` 등 `decide`, `evidenceForClaim` (lemma4_13/4_18/A_7/cor4_25만 연결). **순수 스캐폴딩** (새 수학 0).
- 27535-28092 `Mock2EtaPeterssonCarrierExtension`: 실제 객체 사용 — `Mock2...EtaHalfWeight.etaValue := ModularForm.eta`(Mathlib의 진짜 Dedekind η, Mock2.lean L16330에서 확인), 실제 `Γ(2)`, Mathlib의 쌍곡 부피 `volume : Measure ℍ`, `Metric.closedBall I Y` 절단. `inverseEtaSection = 1/η`의 `ContMDiff`·공변성(`field_simp`)·묶음 descent (`inverseEtaBundleLift_invariant`), `inverseEtaSection_memLp`(콤팩트⇒유계⇒`MemLp.of_bound`, 진짜 소규모 증명), `etaCoreToL2_inner_eq_truncatedPeterssonInner`(`L2.inner_def`+a.e. congr). `etaCoreImageInclusion_denseRange`는 완비화를 closure로 *정의*했으므로 정의상 참(T, docstring이 이를 명시 — 정직). `concrete_inverseEta_petersson_carrier` (L28070) = 7개 기존 사실의 ∧ 묶음.
- 28116-28555 `Mock2EtaCovariantDerivativeExtension`: `smoothInvariantScalars`/`smoothEtaCovariantSections` 부분모듈, `etaGaugeEquiv`(η 곱/나눗셈의 실제 선형동형), **`rawDifferential_deck_comp`(L28344): `mfderiv_comp_apply` 체인룰로 불변 스칼라의 `dg`가 deck pullback 불변** — 진짜(소규모) 다양체 미적분. `etaGaugeDifferential_covariant`(L28471) η⁻¹dg의 정확한 multiplier 공변성 — 수식 검산 결과 정확(η(γτ)⁻¹dg(τ) = (η(τ)/η(γτ))·η(τ)⁻¹dg(τ)). docstring은 "holomorphic (complex-smooth)… No Green identity, real-smooth de Rham…"라고 범위를 정직히 한정.
- 28561-29061 `Mock2EtaH1GraphCompletionExtension`: one-form 섬유 `ℂ →L[ℂ] ℂ`의 evalOne 등거리(`scalarOneFormValue_norm_eq_norm_evalOne`, 진짜·초등), `etaH1Core Y` (g/η, η⁻¹g′ 둘 다 L²), 그래프 `WithLp 2 (L² × L²)`, `etaH1GraphNorm_sq`(WithLp 항등식). **`EtaH1Completion`과 `EtaDerivativeGraphCompletion`은 같은 식의 두 abbrev → `etaH1Completion_eq_derivativeGraphCompletion := rfl`, 동형 = `LinearIsometryEquiv.refl` (T)**; docstring이 "honest reflexive linear isometry"라고 명시(정직하나 내용 없음). 명시적 원소는 `constantOneInvariant`(g=1, 도함수 0)뿐 — 도함수 성분이 0이 아닌 원소는 하나도 제시되지 않음.
- 29067-29630 `Mock2EtaQuotientMeasureExtension`: 실제 궤도몫 `Γ(2)\ℍ`의 기존 coinduced σ-대수 사용(`gamma2Quotient_measurableSpace_eq_map := rfl`), 공 제한 측도의 pushforward(“fundamental domain 아님, 반경마다 대표 중복 가능” 정직 명시), `quotientMap_measurePreserving`, `quotientPullbackL2` = `Lp.compMeasurePreservingₗᵢ` (진짜 Mathlib 사용), `descendInvariant_memLp_iff`(`memLp_map_measure_iff`), η-자명화 `ηf`의 Γ(2) 불변성·L²·몫 L² 클래스와 pullback a.e. 복원(L29438, 진짜 소규모 증명), 묶음값 section의 descent·가측성. 견실한 측도론 배관(U), 단 해석적 추정 없음.
- 29652-29782 `Mock2PaperGeometryNoGoExtension`: `naiveHeightSublevel_half_not_invariant`(Mock2의 하삼각 원소로 Im=1/5 점 → i, 진짜 소규모 no-go), `horizontal_tangential_ne_normal` (ℝ×ℝ의 `.1 ≠ .2` — T), `CorrectedFirstOrderData`(데이터 전용, Prop 필드 없음).
- 29812-30277 `PaperGroundShiftedGapCorrectionExtension`: **`BetaBaselineCountermodel`**: diag(100, 201/2), α=c=1, β=0에서 논문 Prop 4.23/Thm A.7의 세 전제(form domination, complement coercivity, β≤λ0) 모두 성립하나 결론 αc ≤ gap(=1/2) 실패 → `printedBetaGapInference_refuted` (L30033). 바닥 상태가 단순(simple)인 모델이므로 앞선 ground-multiplicity 반례(Fin 3)와 독립인 **두 번째 반박** — 개념적으로 정확(전제가 λ0의 상한을 주지 않음). 증명은 `norm_num`/`nlinarith`. 교정 정리 `every_offGround_real_eigenvalue_gap_ge`(유계, RCLike) / `pmap_every_offGround_real_eigenvalue_gap_ge(_of_selfAdjoint)`(LinearPMap): 대칭성 ⇒ 서로 다른 고유공간 직교, Rayleigh ⇒ δ ≤ μ−λ0. 증명 정확하나, 가설 `HasGroundShiftedComplementCoercivity T λ0 δ`(‖x‖²δ ≤ ⟨x,Tx⟩−λ0‖x‖² on (λ0-고유공간)ᗮ)는 자기수반·이산 스펙트럼에서 "λ0 밖 스펙트럼 ≥ λ0+δ" 즉 **간극 자체의 변분형(min-max) 재진술 → NEAR-CIRCULAR**. 
- 30302-30806 `P1NotationFirewall`: `QSector`(charge/coupling/holonomy) 귀납형과 태그 접근자 ~25개 `rfl` simp 보조정리, 생성자 disjoint/injective (T, 타입 위생). `CuspLabel.sigmaInvMatrix`: ∞, S=[[0,−1],[1,0]], [[0,−1],[1,−1]] — 각각 0, 1을 ∞로 보냄을 검산, det=1, width=2 (Γ(2) 세 첨점 폭 2 — 정확; 최소성은 "여기서 주장 안 함" 명시). `localCuspParameter_norm_lt_one`(Mathlib `norm_qParam_lt_one`), `standardQParameter_does_not_descend_to_Gamma2Quotient`(L30753, 진짜 소규모). `Certificate : Prop` 7필드 무조건 inhabitant — 모두 증명된 정리(DISCHARGED). `instDecidableEqQSector := Classical.decEq` (무해).
- 30812-31405 `P1MatterGaugeDirichletFirewallExtension` (31401 이후는 part3 범위): `MatterField Y := EtaH1Completion Y`; 게이지 carrier = `Lp (WithLp 2 (ℂ×ℂ)) 2` — **자명한 아벨(abelian) ℂ² 다발**, deck 공변성 없음(docstring "cover carrier, descent 아님" 정직). `IsGaugeDeckPullbackRepresentation`/`GaugeDeckCovariantSubmodule`는 *공급될* `deckPullback`에 매개화 — 본 범위에서 구성되지 않음. `CoulombGaugeSlice := divergence.ker` (임의 공급 CLM; 0을 넣으면 전체 공간). `coupledState_matter_type : u.fst ∈ ⊤` (`change True; trivial` — T). `TypedInteraction`/`MatterHamiltonianOperator`는 데이터 전용 구조. Dirichlet/Neumann/Robin domain = 공급된 trace CLM의 kernel, 폐집합성(`isClosed_ker`) 1줄. `IsInteriorCompactSmoothCore isSmooth hasCompactSupportInInterior core` — 두 술어가 **자유 매개변수**라 `fun _ => True`로 자명히 충족 가능 → 인증 의무로서 공허.

### 2. 헤드라인 정리 (27386–31400)
| 행 | 정리 | 상태 |
|---|---|---|
| L28070 | `concrete_inverseEta_petersson_carrier` (콤팩트·유한측도·1/η∈core·내적=적분·closed·injective·dense) | U (얇음; dense는 정의상) |
| L28344 | `rawDifferential_deck_comp` (불변 g의 dg가 deck pullback 불변, `mfderiv` 체인룰) | U (진짜, 소규모) |
| L28471 | `etaGaugeDifferential_covariant` (η⁻¹dg의 multiplier 공변성) | U |
| L28309 | `etaGaugeEquiv` (불변 스칼라 ≃ₗ η-공변 section) | U |
| L29037 | `concrete_inverseEta_H1_graph_completion` (H1 = graph closure, `refl` 동형 포함) | U/T 혼합 |
| L29241/29438 | `quotientPullbackL2`(등거리) / `quotientPullback_etaTrivializedQuotientL2_ae` | U |
| L29609 | `concrete_truncated_eta_quotient_layer` | U (얇음) |
| L29715 | `naiveHeightSublevel_half_not_quotientPreimage` | U (소규모 no-go) |
| L30033 | `printedBetaGapInference_refuted` (Prop 4.23 β-baseline 추론 반박, 단순 바닥) | U (toy 반례, 개념적으로 정확) |
| L30113/30227/30240 | `every_offGround_real_eigenvalue_gap_ge`, `pmap_every_offGround_real_eigenvalue_gap_ge(_of_selfAdjoint)` | C (가설 NEAR-CIRCULAR) |
| L30753 | `standardQParameter_does_not_descend_to_Gamma2Quotient` | U |
| L30795 | `P1NotationFirewall.certificate` | U (DISCHARGED 묶음) |
| L31399 | `dirichletCore_le_traceKernel` | C (hTraceZero, 1줄) |

### 4. 가설·인증 구조 분류 (27386–31400)
- `HasGroundShiftedComplementCoercivity` / `HasPMapGroundShiftedComplementCoercivity` (L30064/30163): **NEAR-CIRCULAR** — 질량간극의 변분형 그 자체. 증명은 이를 고유벡터에 적용하는 Rayleigh 한 줄.
- `IsSymmetric` / `IsFormalAdjoint` / `IsSelfAdjoint` (hsymm, hT): SUBSTANTIVE(표준).
- `IsGaugeDeckPullbackRepresentation` (L30893): SUBSTANTIVE이지만 **미구성·미사용**(accessor 2개만). 게이지 "quotient-ready" 층 전체가 존재하지 않는 객체에 매개화.
- `divergence`, `cuspTrace`, `conormalTrace` (임의 CLM 입력): 가설이 아니라 데이터 — trace 정리 없음을 docstring이 정직히 명시. 단 아무 CLM(0 포함)이나 허용되므로 "Coulomb slice", "Dirichlet domain"이라는 이름은 내용을 보장하지 않음.
- `IsInteriorCompactSmoothCore` (L31344): **공허(trivially satisfiable)** — 술어가 매개변수라 True로 충족; 인증 의무 역할 못 함. (모순은 아니므로 엄밀히 SUSPECT-VACUOUS는 아니고 "무내용 술어".)
- `hTraceZero` (L31402): SUBSTANTIVE 입력(임의 데이터에 대한).
- `P1NotationFirewall.Certificate` (Prop 구조, L30775): **DISCHARGED** (L30795 무조건 inhabitant, 각 필드 실증명).
- `TypedEvidenceClosedPureDiscreteGapExtension.Certificate`: DISCHARGED/중복 스캐폴딩.
- `PrintedBetaGapInference` (L30021): 반박됨(부정 증명) — 고정 모델 위의 명제이므로 "논문 일반 추론 반박"으로서는 정당(전칭 추론의 반례 1개면 충분).
- **CIRCULAR(정확히 결론=가설) 사례는 본 범위에 없음.**
- 참조 인스턴스: `inverseEtaSection = 1/η`는 **진짜 비자명 객체**(Mock1_Advanced식 영(0) 인스턴스 아님) — 긍정적. 반면 `constantOneInvariant`(g=1)는 H1 그래프의 도함수 성분이 0인 퇴화 증인이며, 도함수가 0이 아닌 core 원소는 제시되지 않음. `standardCuspData`는 실제 SL(2,ℤ) 행렬(진짜). `BetaBaselineCountermodel`은 의도된 2×2 toy 반례.

### 5. 정의 충실도 (27386–31400)
- 진짜: η = `ModularForm.eta`, Γ(2), 쌍곡 부피, `mfderiv`, 궤도몫과 그 σ-대수, `Lp`, `WithLp`, `qParam`. 상위 수준 Mathlib 개념 사용은 모범적.
- **문제 1 (holomorphic 제한)**: `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞`는 ℂ-모델에서 *정칙(holomorphic)* 을 뜻함. 따라서 `etaSmoothAutomorphicCore`(L27763)와 `smoothInvariantScalars`(L28138)는 정칙 함수 공간이고, "Petersson completion"은 공 위 L²에서 정칙 section들의 닫힌 부분공간(Bergman형)이지 모든 L² section 공간이 아님. "H1 graph"도 ∂(정칙 도함수)만의 그래프이며 실 Sobolev H¹이 아님. 28105 docstring은 holomorphic임을 밝히지만 27537–27558·28567–28590·30821("A half-weight matter field is an element of the concrete inverse-eta H1 graph completion")은 "smooth"라고만 써 **물질장 공간이 정칙 section의 폐포라는 사실이 은폐됨**. 우려(미검증, Lean으로 확인 안 함): 정칙 함수 폐포 위에서 경계 trace=0인 Dirichlet 영역은 경계 유일성 정리 때문에 {0}로 퇴화할 가능성이 큼 — part3/리드가 이후 `HD`(Dirichlet matter Hamiltonian)가 이 `MatterField`를 쓰는지 확인 필요.
- **문제 2 ("Petersson" 오칭)**: `truncatedPeterssonInner`(L27903) = ∫⟨f,g⟩ dμ_hyp, **가중치 y^{k}(여기선 y^{−1/2})나 Hermitian metric이 없음** → 피적분함수가 Γ(2) 불변이 아님. 공 절단이라 불변성이 쓰이지 않아 증명엔 영향 없지만 "actual truncated Petersson pairing"은 과장. 한편 몫 L² 층(L29334)은 |ηf|²(η-자명화)를 쓰므로 두 "Petersson" 노름이 서로 다르며 둘을 잇는 정리 없음.
- **문제 3**: 절단 = 쌍곡 닫힌 공(fundamental domain 아님), 몫측도 = pushforward(중복 계수) — docstring이 정직히 밝힘.
- **문제 4 (게이지)**: 게이지장 = 자명 아벨 ℂ² 다발의 L², deck 공변성·비아벨 구조 없음 → Yang–Mills(비아벨) 게이지장의 충실한 모델 아님; docstring은 "cover carrier"라고 정직히 한정.

### 6. 실질 수학 비중 (27386–31400, ≈4,020행)
- 진짜 (비자명) 증명: Petersson carrier L²/내적(~150), 체인룰 공변성(~150), 몫 측도 descent·pullback(~250), ground-shifted 교정+β 반례(~250), cusp q-parameter/no-descent·height no-go(~120) ≈ **850행 ≈ 21%**.
- 정직한 정의 인프라(부분모듈 레코드, simp/rfl 보조정리, 타입 방화벽, boundary kernel 정의): ≈ 2,200행 ≈ 55%.
- 스캐폴딩/T(TypedEvidence 145행, QSector 태그 접근자, `refl` 동형, `∈ ⊤`, 라벨 `rfl`, ∧-묶음 요약 정리): ≈ 950행 ≈ 24%.
- 선언 통계(decls JSON, 범위 내 478 decl): theorem 265 (long 123, trivial_tactic 72, short 66, accessor 18), def 134, abbrev 53; 본문이 `rfl`로 끝나는 decl 76개.

### 7. 오류·과장 (27386–31400)
- L27901 "The actual truncated Petersson pairing" — 가중치 없음(위 문제 2).
- L27550–27558, L28575–28577, L30822 — "smooth"가 실제로는 holomorphic(위 문제 1), 물질장 공간 성격이 과장/은폐.
- L29034 `concrete_inverseEta_H1_graph_completion` "single unconditional presentation theorem": 7개 연언 중 `Function.Bijective (refl)`, closure의 closed/dense 등 다수가 정의상 참 — 내용 대비 표제 과장.
- L29806 docstring "They prove the gap estimate for every distinct point eigenvalue" — 사실이나, 가정이 곧 간극의 변분형임을 명시하지 않음(경미한 과장).
- 수학적으로 **틀린** 진술은 발견 못 함 (cusp 행렬, width 2, 공변 인자, β 반례 수치 모두 검산).

### 8. 코드 품질 (27386–31400)
- 장점: 매우 명료한 docstring, 범위 한정 문구(“not a fundamental domain”, “no trace theorem is stored”) 일관; Mathlib API(`Lp.compMeasurePreservingₗᵢ`, `memLp_map_measure_iff`, `mfderiv_comp_apply`) 정확한 사용; 중첩 Prop 필드 없는 데이터 구조.
- 단점: 네임스페이스마다 `abbrev H/Gamma2/Gamma2Quotient` 재선언, `IsGamma2Invariant` 2중 정의(L28129, L29283), dense-range 증명 복붙(L28025 ≈ L28962), `etaPeterssonCompletionCompleteSpace := inferInstance`류 무의미 def, `concrete_*` ∧-묶음 요약, QSector 태그 rfl 보조정리 다량. Mathlib PR 후보: `scalarOneFormValue_norm_eq_norm_evalOne`(1차원 쌍대 노름), 일반화된 "symmetric T의 ground-shifted coercivity ⇒ off-ground 고유값 간극" 정도(소품).

### 10. 잠정 점수 (27386–31400만)
- 형식적 건전성 9 — 0 sorry/axiom, 컴파일 확인됨, local instance는 가측구조 재노출 1개뿐, `Classical.decEq` 무해.
- 조건부 인증 정직성 7 — scope docstring은 모범적이나 ground-shifted coercivity는 NEAR-CIRCULAR, `IsInteriorCompactSmoothCore` 무내용, "Petersson"/"smooth" 표기 과장.
- 수학적 실질성 4 — 진짜 객체(η, Γ(2), 쌍곡측도, mfderiv)를 쓰지만 증명은 얇고 해석적 추정(trace, Gårding, 콤팩트성) 전무; 완비화/조밀성은 정의상.
- 정의 충실도 5 — 기초 객체는 진짜, 그러나 정칙 제한·무가중 "Petersson"·자명 아벨 게이지 carrier·공 절단.
- 코드 품질·유지보수성 6 — 깔끔·잘 문서화, 반면 반복 abbrev·복붙·태그 boilerplate.
- 종합 5.5 — "구체적 모듈러 기하 배관 + 정직한 방화벽"이며 질량간극 쪽은 β-baseline 반례(가치 있음)와 근-순환적 교정 정리.

## 범위 전체 요약 (15736–31400, ≈15,665행)

**성격**: 이 구간은 QYM의 "추상 함수해석 층"(15736–27385)과 "구체 모듈러 기하 배관 층"(27535–31400)으로 나뉜다. 전자에는 이 모듈에서 가장 실질적인 수학이 있다: 실/복소(RCLike) Friedrichs형 구성(Gårding 하 Lax–Milgram로 (A+μ)⁻¹ 구성, 최대대칭성으로 self-adjoint 직접 증명, L20718–21398 / L22826–24005), 유계 대칭 섭동의 self-adjointness(L21679–), KLMN 유사 form-small 섭동(L21964–), **compact symmetric 연산자의 0에서 떨어진 점 스펙트럼 유한성(L25057–25368, `awayFromZeroPointSpectrumFinite_of_compact_symmetric` — 이전 가설 `AwayFromZeroPointSpectrumFinite`를 DISCHARGED)**, `HilbertBasis.mkOfOrthogonalEqBot`로 고유기저 구성(L26414–). 이들은 Mathlib PR 후보급이다.

**핵심 한계**: (1) 질량간극 관련 "정리"는 모두 `HasGroundComplementCoercivity`·`HasGroundShiftedComplementCoercivity`·균일 coercivity c 등 **간극 자체의 변분형을 가설로** 받는다(NEAR-CIRCULAR; L19626–, L26835–27069, L30064–30250). 정확히 결론=가설인 CIRCULAR 사례는 이 구간에서 발견되지 않았다. (2) 이 추상 정리들을 논문의 구체 q-YM Hamiltonian에 연결하는 다리는 없다 — 구체 층(27535–)은 η-공변 정칙 section, 공 절단 L², graph closure, 공급형 trace/divergence 슬롯까지만 구성하며, trace 정리·Gårding 부등식·콤팩트 매장·Hamiltonian 자체는 없다(docstring이 이를 정직히 밝힘). (3) 구체 물질장 공간은 정칙 section의 폐포이고 "Petersson" 내적에 가중치가 없다(정의 충실도 결함). (4) 스캐폴딩: TypedEvidence 레지스트리 6개(≈1,430행), PaperNormalized 별칭 래퍼(≈2,300행), 실/RCLike Friedrichs 중복(~700행).

**긍정**: 논문 Prop 4.23/Thm A.7의 추론 오류를 두 독립 반례(ground multiplicity Fin 3; 단순 바닥 β-baseline 2×2, L30033)로 정확히 지적하고 교정형을 제시한 점, docstring의 범위 한정이 일관되게 정직한 점, Mock1_Advanced식 영(0) 인스턴스 대신 진짜 1/η를 증인으로 쓴 점.

**실질 수학 비중(행 기준, 추정)**: 15736–27385 ≈ 35–40%, 27386–31400 ≈ 21% → 구간 전체 **≈ 30–35%**. 나머지는 정직한 정의 인프라(~35%)와 스캐폴딩/래퍼/T(~30%).

**구간 전체 잠정 점수 (15736–31400)**
- 형식적 건전성 9 — 탈출구 없음, 컴파일 확인, Classical.choose는 존재 증명 후 선택(정당).
- 조건부 인증 정직성 6.5 — docstring 정직, CIRCULAR 없음; 그러나 간극 정리들의 가설이 사실상 간극이며, "Unconditional"/"corrected" 표제가 추상 FA 의미임을 독자가 놓치기 쉬움.
- 수학적 실질성 6 — Friedrichs 구성·Riesz–Schauder형 유한성·고유기저·섭동 이론은 진짜이고 비자명; q-YM 고유의 해석은 전무.
- 정의 충실도 6 — 추상 층은 Mathlib `LinearPMap`/`IsSelfAdjoint`/`IsCompactOperator`로 충실; 구체 층은 정칙 제한·무가중 Petersson·아벨 자명 게이지·공 절단.
- 코드 품질·유지보수성 5.5 — 개별 증명은 깔끔하나 거대 단일 파일, 중복(실/RCLike), 레지스트리·래퍼 boilerplate.
- 종합 6.

### 커버리지 로그 (이어서)
- 27386–28385 정독 (TypedEvidence 끝, PeterssonCarrier, CovariantDerivative 전반)
- 28386–29485 정독 (CovariantDerivative 끝, H1GraphCompletion, QuotientMeasure 전반)
- 29486–30485 정독 (QuotientMeasure 끝, PaperGeometryNoGo, GroundShiftedGapCorrection, P1NotationFirewall 전반)
- 30486–31405 정독 (P1NotationFirewall 끝, P1MatterGaugeDirichletFirewall 31405까지)
- 보조: decls_cls.json 범위 집계, Mock2.lean L16330 `etaValue := ModularForm.eta` 확인, 범위 내 "holomorphic"/가중치 grep.
- 스킴(skim) 구간: 없음. 15736–27385는 이전 감사자 노트에 의존(재독 안 함).
