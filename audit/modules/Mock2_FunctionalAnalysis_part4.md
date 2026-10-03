# Mock2_FunctionalAnalysis — Part 4 구간 감사 (lines 47401–63138, 최종 구간)

감사자: range auditor K=4. 원본 `.lean`을 47401–63138 전부 순차적으로 읽었다(커버리지 로그는 맨 끝에).
선행 노트 `FA_notes.txt`(1–15899)와 필요한 상류 정의(grep으로 해당 선언만 확인)를 참조함.
lake/lean 미실행(컴파일 성공은 lead가 확인: 0 errors).

---

## 0. 구간 요약 (한 단락)

이 구간은 모듈의 **최종 기능해석 층**이다. 핵심 산출물은 (i) 실제 Γ(2)·실제 η-승수·실제 판별식 포텐셜
V = y¹²|Δ|² (Mathlib `ModularForm.discriminantCuspForm`의 Petersson 노름)에 대한 **약 Schrödinger 작용소의
무조건 Fredholm 대안**, (ii) 그 핵심 입력인 **포텐셜 작용소의 콤팩트성**(국소 Rellich를 직사각형 Fourier
급수로 직접 증명 + cusp 꼬리 감쇠), (iii) 첫째 계 raising/lowering 작용소의 **strong = weak (최소 = 최대)**
정리(몫 공간 위 Friedrichs 모리파잉 + Γ(2)-불변 분할의 단위로 접합), (iv) 형식방법 자기수반 실현의
유계 resolvent·점스펙트럼 성질, (v) 논문 정정/반례 "firewall"과 **논문 최종 주장(Kuznetsov 경유 모순)이
형식화되지 않았음을 스스로 명시하는 의존성 감사**이다. 순환 가설·퇴화 인스턴스는 발견되지 않았다.

---

## 2. 헤드라인 정리 (구간 내)

| # | 선언 (line) | 진술 (요약) | 상태 |
|---|---|---|---|
| 1 | `fredholmDefect_rangeOrthogonal_finiteDimensional` (47786) | K 콤팩트 ⇒ `FiniteDimensional ℂ (fredholmDefect K).rangeᗮ` (range(I−K)ᗮ 위에서 ‖u‖≤‖Ku‖ → 단위구 totally bounded) | U (진짜, 업스트림 가치) |
| 2 | `ShiftedCompactDecomposition.cokernel_finiteDimensional` (47996) | `FiniteDimensional ℂ (W ⧸ A.range)` (대수적 cokernel) | U (분해 구조 주어지면) |
| 3 | `integrable_fullPlaneTest_mul_kernel_mul_translate` (49059) | K∈L¹(ℂ), v∈C_c^∞, u∈L² ⇒ (x,t)↦v x·K t·u(x−t) 가 ℂ×ℂ에서 적분가능 | U (과거 blocker; 올바른 Tonelli/Hölder 논증) |
| 4 | `friedrichsMollifierAction_ae_eq_mollifiedRepresentative` (49332) | Hilbert값 Bochner 모리파이어 작용 = 점별 합성곱 (a.e.) | U |
| 5 | `strongCoreEquation_iff_weakEquation` (48955) | 매끈한 코어 원소 u에 대해 strong 방정식 ⇔ H⁻¹ 약 방정식 | U |
| 6 | `completedLiteralStagePlaneBase_isCompact` (54574) / `graphLiteralStageRestriction_isCompact_unconditional` (54809) | 그래프 완비화 → 리터럴 3-cusp stage L² 제한이 콤팩트 (Rellich) | U |
| 7 | `graphPotentialOperator_isCompact_unconditional` (55813) | `IsCompactOperator (graphPotentialOperator n)` | U |
| 8 | `unconditionalFredholmData` (56376), `weakSchrodinger_solvable_iff_adjointKernel_orthogonal_unconditional` (56430), `weakSchrodinger_kernel/adjointKernel/cokernel_finiteDimensional` (56405–56427), `weakSchrodinger_range_isClosed` (56390) | 실제 PDE 작용소의 Fredholm 대안 전체 패키지 | **U (모듈 캡스톤)** |
| 9 | `modularMassResolvent_isSelfAdjoint` (57510), `neg_discriminantMassShift_mem_partialResolventSet` (57408), `norm_modularMassResolvent_le_one` (57463) | 자기수반 실현의 −m 에서의 유계·자기수반·축약 resolvent | U |
| 10 | `modularAssociatedOperator_eigenvalue_re_lower_bound` (50559), `..._distinct_eigenspaces_orthogonal` (50543) | 고유값 실수·하한, 고유공간 직교 | U (초등적) |
| 11 | `smoothCore_operatorCore_iff_minimal_eq_maximal` (50334), `modularAssociatedOperator_eq_maximal_iff_smoothCoreIsOperatorCore` (57604) | 2계 작용소 코어성 ⇔ 본질적 자기수반 ⇔ 연관=최대 (동치만, 명제 자체는 미증명) | U(동치)/목표 명제 미해결 |
| 12 | `gammaTwoEffective_eq_one_of_smul_eq` (58837), `gammaTwoReducedChartCompletedCarrier_isFundamental` (57894) | Γ(2)/±1 작용의 자유성; 차트를 포함하는 기본영역 구성 | U |
| 13 | `exists_quotientCompatibleFiniteReducedChartLocalization` (61968) | Γ(2)-불변·매끈한 유한 분할의 단위 (궤도 포화 위에서 합=1) | U |
| 14 | `strongCrossAdjointAt_unconditional` (63072) | `closedRaise n = (−L)† ∧ closedLowerFromSucc n = (−R)†` (첫째 계 최소=최대) | **U (캡스톤)** |
| 15 | `jointGraphCoreDensityAt_unconditional` (63117), `graphCompletionEquivWeightedWeak_unconditional` (63125) | 매끈한 코어의 3좌표 동시 조밀성; 그래프 완비화 ≅ₗᵢ 약 가중 Sobolev 공간 | **U (파일 최종 선언)** |
| — | `p10P11_honestDependencyAudit_endpoint` (57088) | 분류표: Kuznetsov·Plancherel·Kloosterman 소거 = `.externalMathematics`, 최종 모순 = `.logicalReductionOnly` | T(메타데이터, `rfl`) |
| — | `false_of_exactLowerUpperCrossoverInput` (48117), `no_statistic_between_explicitProfiles` (56311) | 가설에 모순을 내장/장난감 프로파일(2 vs 1/(m+1)) | T (정직하게 표기) |

### 모듈의 최종(capstone) 주장과 무조건성
모듈 기능해석 층이 **최종적으로 주장하는 것**:
1. 모든 n∈ℤ, t∈ℝ 에 대해 실제 약 작용소 `weakSchrodingerOperator n t : ActualHOne n →L ActualHMinusOne n`
   (그래프 에너지 − t·V-포텐셜)는 닫힌 치역, 유한차원 핵/여핵, `range = (ker A†)ᗮ`, 정준 해와 노름 상한을
   갖는다 — **무조건**(가설 0개). 핵 자명성(`HasTrivialKernel`)이 주어지면 연속 동형까지(이 부분은 **조건부**,
   핵 자명성은 증명되지 않음 — 정직히 명시).
2. 첫째 계 raising/lowering의 strong=weak(`strongCrossAdjointAt_unconditional`)와 동시 그래프 조밀성 및
   약 Sobolev 공간 동일시 — **무조건**.
3. 형식방법 자기수반 실현 + 유계 resolvent — **무조건**. 반면 2계 작용소의 본질적 자기수반(매끈한 코어가
   operator core인가)은 **증명되지 않았고** 동치 명제로만 기록.
4. 논문의 산술/스펙트럼 최종 주장(반정수 Kuznetsov 공식, Eisenstein 정규화, 산란 Plancherel, multiplier
   Kloosterman 소거, 하한·상한 교차 → 모순)은 **형식화되지 않았으며**, 파일이 이를 `AuditDisposition`
   `.externalMathematics`로 명시. 즉 "Mock2의 해석적 최종 결론"은 Fredholm/자기수반 층에서 멈춘다.

---

## 3. 탈출구/신뢰기반 (구간 내)
- sorry/admit/axiom/native_decide/opaque/unsafe: 0 (주석 제외 grep). `set_option maxHeartbeats`: **구간 내 0개**.
- 커스텀 macro/syntax/elab: 없음. `decide` 대형 항 없음.
- `#print axioms` 184줄(약 25개 `AxiomAudit*` 네임스페이스) — 감사용 출력일 뿐 논리적 영향 없음.
- `Classical.choose` 28회 — 전부 **증명된 존재명제**(cthickening 버퍼, 높이 상·하한, 분할의 단위, Fourier 반경, cusp 레벨)에서의 선택. 데이터 날조 없음.
- `private theorem gammaTwo_mem_stabilizer_fd_eq_one_or_neg_one` (58738) — 같은 증명이 57749 내부에도 복제됨(품질 문제일 뿐).
- `@[reducible] weakAntiOperatorSubFrozen` 등 "frozen" 보조정리(55637–55757): elaboration 성능 우회. 건전성 문제 없음.

## 4. 조건부 인증 감사 (구간 내 모든 가설/인터페이스)

| 가설/인터페이스 | 위치 | 분류 | 근거 |
|---|---|---|---|
| `hcompact : IsCompactOperator (graphPotentialOperator n)` | 48050–48074 | **DISCHARGED** | 55813 `graphPotentialOperator_isCompact_unconditional`, 56363 재노출 |
| `StrongCrossAdjointAt n`, `(n+1)` (in `jointGraphCoreDensityAt_of_strongCrossAdjoints`) | 49587 | **DISCHARGED** | 63072 → 63117 |
| `RaisingCompactFriedrichsPeriodizationAt`/`Lowering...` (상류 Prop, 37485) | 62930, 62999 | **DISCHARGED** | 국소 Friedrichs + 유한 접합으로 증명 |
| `RaisingInvariantCutoffGraphControlAt`, `AmbientTestPhysicalGaugePeriodization` (상류) | 63075–63078 사용 | DISCHARGED (상류 42070, 38202) | 다른 구간 감사자 확인 권장 |
| `CompactChartBuffer` (structure) | 48181 | DISCHARGED | `compactChartBuffer`(48188), Mathlib `exists_cthickening_subset_open` |
| `IsReducedChartGaugeModel` (Prop) | 59775 | DISCHARGED | `periodizedPhysicalCore_isReducedChartGaugeModel`(59872), signed/raised/lowered 버전, `invariantScalarCoreOperator_isReducedChartGaugeModel`(62435) |
| `HasEssentialSupportIn` (Prop) | 59216 | DISCHARGED (사용처마다) | `fullPlaneTestMulL2_hasEssentialSupport` 등 |
| `IsPlanarAffineWeakGraphOn` (Prop) | 58578 | DISCHARGED | `raisingMaximalAdjoint_isPlanarAffineWeakGraphOn_reducedChart`(60165) |
| `BoundedPartialResolventAt` (structure, 4 필드) | 57181 | DISCHARGED | `modularBoundedPartialResolvent`(57390) — 실제 Lax–Milgram 역 |
| `IsEvenEntireGaussianStripTest` | 55966 | DISCHARGED | 가우시안 inhabit(55976); 스펙트럼 공식 필드 없음 |
| `HasTrivialKernel (weakSchrodingerOperator n t)` | 56498–56523 | SUBSTANTIVE(미증명, 정직) | 핵 자명성은 별도 정리 필요라고 docstring 명시 |
| `SmoothCoreIsOperatorCore n t` | 50244 | SUBSTANTIVE(미증명 목표, 가설로 쓰이지 않음) | 동치만 증명 |
| `hGap : ... ≠ maximal...` | 50344, 57623 | 대우 형태 보조정리(T) | — |
| `ExactLowerUpperCrossoverInput` | 48109 | **사실상 CIRCULAR/자명** (세 번째 성분이 첫 두 성분과 즉시 모순) — 그러나 "final logical reduction only"로 **정직하게 표기**, 산술 입력 inhabit 안 함, `compatibleAudit_not_exactLowerUpperCrossoverInput`(56897)로 비자명 모델이 이를 만족하지 않음을 보임 | 
| `HasUniformLowerActivity` | 48124 | 정의적 Prop, 장난감 inhabit(56270, 가우시안 유한창) | T |

**reference/예시 인스턴스**: 퇴화(0 함수·자명 구간) 인스턴스 **없음**. 대신 장난감 반례(상수 산란 jet,
x², 상수 위상합, 2 vs 1/(m+1))는 모두 "반례/모델"로 명시. 실제 대상(Δ, η-승수, Γ(2) 기본영역,
Mathlib Fourier 기저)이 계속 사용된다. 주의: `finiteHalfIntegralKloostermanSum`(56124)·
`reducedResidueHalfPhaseSum`(56702)은 이름과 달리 **실제 반정수 가중 Kloosterman 합이 아닌 임의의 유한 위상합**
(docstring은 "not a proved Kuznetsov Kloosterman sum"이라 명시하지만 첫 번째 이름은 오해 소지).

## 5. 정의 충실도
- 작용소론: Mathlib `LinearPMap`(graph, adjoint `†`, closure, `HasCore`, `IsSelfAdjoint`), `IsCompactOperator`, `ContinuousLinearMap.adjoint`, `Submodule.orthogonal` — **충실**.
- 함수공간: `MeasureTheory.Lp` (L², L∞, Hölder `lpPairing`, `holder`), Mathlib 테스트 함수 `TestFunction`/`FullPlaneTest`, `UnitAddTorus.mFourier`/`mFourierBasis` — **충실**.
- 기하: Γ(2) 효과적 작용, `IsFundamentalDomain`, Mathlib `ModularGroup.fd`·`cases_of_mem_fd_smul_mem_fd` — **충실**.
- 포텐셜: `upstairsPotential z = ‖petersson 12 Δ Δ z‖` (19936) — **실제 대상**, 0 포텐셜 회피 명시(`upstairsPotential_pos`).
- 프록시: `partialEigenspace`/`HasPartialEigenvalue`/`BoundedPartialResolventAt`는 Mathlib에 비유계 스펙트럼 API가 없어서 직접 정의 — 정의 자체가 표준 개념과 일치(축약 없음). Kloosterman 이름의 위상합은 프록시이며 실제 대상과의 다리 **없음**(정직 표기).

## 6. 실질 수학 내용
진짜 비자명 증명(대표):
- Fredholm 유한차원성 직접 증명(47712–48003): 고유공간 유한차원(restrict + `isCompactOperator_id_iff_finiteDimensional`), range(I−K)ᗮ 유한차원(uniform embedding + totally bounded) — 콤팩트 adjoint API 없이.
- Bochner/Fubini 다리(49040–49369), Petersson 피벗 매장·최소/최대 작용소(49773–50350).
- **Rellich**(50663–54815): reduced-chart 분할의 단위로 만든 cutoff, 그래프 밀도의 점별 지배(`norm_height_mul_dx_sq_le_...`), 유한 Γ(2)-평행이동 덮개, 쌍곡/유클리드 측도 변환, 평면 H¹ ≤ C‖u‖², 직사각형→2-토러스 주기화, 평면파 정규직교·IBP·Fourier 계수 미분 공식, 꼬리 |ĉ_k| ≤ (2π(N+1))⁻¹(|∂x^|+|∂y^|), 작용소 노름 수렴 ⇒ 콤팩트.
- 판별식 hard truncation(54831–55818): L∞ 곱셈자, ε_N=1/(N+1) 꼬리 상한, 노름 수렴.
- 몫 공간 Friedrichs(57683–63082): Γ(2) 자유성, 차트 완비 기본영역, 차트 L² 하강, 평면 국소화 Leibniz, essential support 대표 교체, 주기화가 차트 위에서 seed와 일치, 최대 adjoint → 평면 약그래프, 국소 Friedrichs 근사, 불변 분할의 단위(분모 B + (1 − smoothTransition(2Re B −1)) ≠ 0), 불변 스칼라 곱셈자, 쌍대성으로 전역 극한 식별, 그래프 단가성으로 미분 좌표 재구성.

과거 blocker 평가:
- `integrable_fullPlaneTest_mul_kernel_mul_translate`(49059): **진짜 해석학**. `integrable_prod_iff'`로 (a) 각 t-slice 적분가능(평행이동 L² 벡터와 Hölder), (b) 바깥 함수 t↦∫‖v x K t u(x−t)‖dx 를 ‖K t‖·‖lsmul‖·‖v‖₂·‖u‖₂로 지배(`norm_holder_apply_apply_le`, `DomAddAct.norm_vadd_Lp`). 수학적으로 정확, 증명 97줄.
- `weightedFull_sub_weightedHard_eq_weightedTail`(55740): **진짜지만 초등적**. 점별 분해 V = V·1_K + V·1_{Kᶜ}(`discriminantFull_eq_hard_add_tail`)와 L∞·L² 선형성으로 (전체 곱셈자) − (hard-stage 작용소) = (tail 곱셈자). 비자명 부분은 hard-stage 인수분해가 전역 운반자 곱셈과 같다는 `discriminantHardStageOperator_eq_weightedHard`(55584, hard 가중치가 리터럴 stage 밖에서 0). "frozen" 보조정리들은 수학 내용 없는 elaboration 우회.

**구간 줄 수 분해(추정, 총 15,738줄)**:
- 주석/docstring/빈 줄: ≈2,690 (17%) [빈 줄 1,269]
- `#print axioms` 및 감사 네임스페이스 래퍼: ≈290 (2%)
- 장난감 반례·정정 firewall·메타데이터 DAG(P10 47408–47688, P11 48092–48155, 55842–56345, 56545–57133): 코드 ≈960 (6%)
- 얇은 래퍼/`rfl` apply 보조정리/재노출(예: 48041–48076, 56355–56543 대부분, 27개 `rfl` 정리 223줄): ≈500 (3%)
- **진짜 해석학 증명 코드: ≈11,300줄 (~72%)** — 이 중 약 1/3이 깊은 핵심(Rellich, Friedrichs 접합, Fredholm), 나머지는 support/측도 bookkeeping(정당하지만 반복적).

## 7. 수학적 정확성 / 과대표기
- 잘못된 진술 **발견 못함**. 오히려 거짓일 진술(컴팩트 resolvent, 이산 스펙트럼 — 유한 부피 비콤팩트 곡면에서는 연속 스펙트럼 때문에 거짓)을 의도적으로 피한다(57135 docstring, 50379 docstring).
- 과대 표기(경미):
  - `finiteHalfIntegralKloostermanSum`(56124): 이름이 실제 Kloosterman 합을 연상시키나 고안된 위상합.
  - `availableFoundation_coexists_with_noCrossover`(56907)·`manuscriptCorrectionFirewall_endpoint`(57066): "endpoint"라는 이름이지만 자명한 반례들의 연언.
  - `false_of_exactLowerUpperCrossoverInput`(48117): 가설이 이미 모순을 담음 — docstring은 정직("the contradiction is immediate").
  - 헤더/섹션 제목 "unconditional"은 실제로 가설 없이 증명됨(확인).
- Fredholm 캡스톤은 "Riesz 동형 − t·콤팩트"의 표준 Riesz–Schauder 이론 적용이므로, 수학적 깊이는 거의 전부 **포텐셜 콤팩트성**과 **그래프 완비화 구성**에 있다(정당한 평가).

## 8. 코드 품질
- 단점: 완전 한정 이름 `Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore` 등을 `open` 후에도 수백 번 반복(가독성 크게 저하); "This fragment is intended to be appended after …" 류의 AI 생성 조각 이음새 주석이 그대로 남음; Γ(2) 자유성 증명 ~70줄 **중복**(57749 vs 58738); raising/lowering 쌍 정리 대부분이 거의 복붙; `#print axioms` 블록이 코드 사이사이에 산재; 단일 파일 63k줄.
- 장점: 증명이 명시적이고 견고한 편(`simp only`, `filter_upwards`, `calc`), 구간 내 heartbeat 상향 없음, docstring이 논리적 지위를 정확히 기술.
- 업스트림 후보: (1) `fredholmDefect_rangeOrthogonal_finiteDimensional`/`compactOperator_eigenspace_finiteDimensional`(I−K의 유한차원 핵·여핵), (2) `integrable_fullPlaneTest_mul_kernel_mul_translate` 일반화(L¹ 핵 × L² 합성곱의 쌍대 Fubini), (3) `partialEigenspace`·`BoundedPartialResolventAt`(LinearPMap 스펙트럼 기초), (4) 직사각형-토러스 Fourier Rellich, (5) `RectangleFourierTail.finiteHilbertProjection_tail_le_of_coeff_sq`, (6) `finset_graph_snd_eq_of_sum_fst_eq`.

## 9. 컴파일
lead 확인: 모듈 전체 0 errors (771 s). 구간 내 위험 신호 없음(heartbeat 상향 0, frozen 우회는 이미 통과).

## 10. 구간 점수 (잠정, 1–10)
- 형식적 건전성: **9** — 탈출구 0, heartbeat 상향 0, 선택은 모두 증명된 존재명제.
- 조건부 인증의 정직성(비순환성): **9** — 모든 해석적 가설이 구간 내/상류에서 discharge; 미해결 목표(핵 자명성, 2계 본질적 자기수반, Kuznetsov 등)는 가설 위장 없이 명시. 감점: Kloosterman 이름 오해 소지, 자명한 "endpoint" 연언.
- 수학적 실질성: **8** — Rellich·Friedrichs·Fredholm이 실제 대상 위에서 진짜로 증명됨. 감점: 논문 최종 산술 주장은 미형식화, 캡스톤 Fredholm 자체는 표준 이론 적용, bookkeeping 비중 큼.
- 정의 충실도: **9** — Mathlib 표준 개념 사용, 실제 Δ/η/Γ(2). 위상합만 프록시.
- 코드 품질·유지보수성: **5** — 장황한 완전 한정명, 조각 이음새 주석, 중복 증명, 거대 단일 파일.
- 종합: **8** — 이 구간은 모듈에서 가장 실질적인 부분이며 정직하게 범위를 제한한다.

---

## 커버리지 로그
- 47401–48500 Read (원본) — P10 cusp 좌표/정정, Fredholm 유한차원, P11 조건부 환원, P3.26 버퍼.
- 48500–49349 Read — P6 strong/weak, Bochner/pointwise 다리.
- 49349–50198 Read — P4 joint density, P9 minimal/maximal.
- 50198–51047 Read — P9 코어 동치, P9 점스펙트럼, P5 cutoff/높이.
- 51047–51896 Read — 그래프 밀도 지배, 유한 덮개, 쌍곡 밀도.
- 51896–52745 Read — 평면 H¹ 적분, 완비 확장, Fourier 박스/모드.
- 52745–53594 Read — 토러스 주기화, 평면파, IBP.
- 53594–54443 Read — Fourier 계수 미분, 정규직교, 꼬리 부등식.
- 54443–55292 Read — Rellich 콤팩트성, stage 제한, hard truncation 시작.
- 55292–55991 Read — hard/tail 분해, 포텐셜 콤팩트성, P11 가우시안.
- 55991–56590 Read — P11 위상합/프로파일, P12 Fredholm 캡스톤.
- 56590–57189 Read — P10/P11 의존성 감사 DAG.
- 57189–57888 Read — P9 resolvent, Γ(2) 자유성(1차).
- 57888–58637 Read — 차트 완비 기본영역, 차트 L² 하강, 평면 국소화.
- 58637–59436 Read — 국소화 마무리, 주기화 차트 항등식, essential support.
- 59436–60235 Read — 약그래프 다리(켤레 테스트).
- 60235–61034 Read — 국소 Friedrichs 근사, 등거리 모델.
- 61034–61834 Read — 모델 노출 극한, 불변 스칼라 주기화, 분할의 단위.
- 61834–62483 Read — 정규화 분모, 불변 곱셈자.
- 62483–63138 Read — 쌍대 식별, 최종 무조건 Friedrichs, strongCrossAdjoint, P4 최종.
- 스킴(grep만): `#print axioms` 184줄은 읽었으나 내용 분석 생략. 상류 선언은 grep으로 개별 확인(19936, 20160, 28127, 36401, 37053, 37472–37579, 42070, 42729, 44559, 45306, 46273–46340, 46886, 46980–47160).
