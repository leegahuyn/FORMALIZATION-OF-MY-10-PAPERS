# Mock2_FunctionalAnalysis — Part 3 (31601–47400행) 범위 감사

감사자: range auditor K=3. 원본 `.lean`을 31230–47420행까지 순차 정독(약 1000행 단위 Read 17회; 31230–31600은 맥락용 선행 독해). 생략·스킴 구간 없음(단, 각 네임스페이스 말미의 `#print axioms` 블록 197행은 목록 확인만). `lake`/`lean` 미실행, 저장소 미수정.

## 0. 범위 개관

이 구간은 논문 정정판 "P3.4–P3.25 / P4.1–P4.2 / P5.1–P5.4 / P6–P7 브리지 / P9" 블록으로, 반정수 무게 eta 승수 고정위상 Maass 상승(R)/하강(L) 연산자의 **(i) Γ(2) 6-타일 다각형 위 전역 Stokes/Green, (ii) 선택 커스프 L² 트레이스 정리, (iii) 최대수반 그래프의 국소화(컷오프)·정칙화(Friedrichs)·주기화 경로, (iv) 독립적으로 정의된 가중 약 Sobolev 공간, (v) 2-토러스 Fourier–Rellich 틀, (vi) 판별식 퍼텐셜 약 Schrödinger 연산자와 폐형식 자기수반 실현(제1표현정리)** 를 다룬다. 문자열 레지스트리·ClaimStatus 원장·"UNCONDITIONAL" 라벨 문자열은 이 범위에 **하나도 없다**. `sorry/admit/axiom/native_decide/opaque/unsafe/implemented_by/maxHeartbeats` 0건; `decide`는 3원소 Finset 등식 1건(32404)뿐.

## 2. 헤드라인 정리 (U=무조건 진짜, C=명명 가설 조건부, A=접근자, T=자명)

| # | 행 | 이름 | 내용(요약) | 상태 |
|---|---|---|---|---|
| 1 | 33349 | `gammaTwoPairedPolygonFluxStokes : GammaTwoPairedPolygonFluxStokes` | Γ(2) 선택 기본영역(6 타일) 위 `∫ y²(∂ₓX+∂ᵧY) dμ_hyp = 0` (매끄러운 몫-콤팩트 Γ(2)-불변 플럭스). 16363에서 가설이던 Prop을 실제 방출 | **U** |
| 2 | 33376, 33397–33404 | `gammaTwoCompactFluxStokes`, `physicalGreenIdentityAt_unconditional`, `physicalGreenIdentity_unconditional` | 콤팩트 플럭스 Stokes ⇒ 고정위상 코어 위 Green 결함 0 | U (재포장은 1–3줄) |
| 3 | 33441 | `physicalRaise_isFormalAdjoint_negativeLower_unconditional` | `(physicalRaise n).IsFormalAdjoint (-physicalLowerFromSucc n)` | U |
| 4 | 32180 | `sum_nativeOrientedActualEdgeContribution_eq_zero` | 실제 변 매개화의 진짜 접벡터·변수변환 t↦−t로 짝지은 변 기여 완전 소거 | C(`IsGammaTwoInvariantFlux`, 입력의 정의적 성질) |
| 5 | 36457 / 36712 | `coreGraphTraceEstimate_unconditional` / `unconditionalCompletedSelectedCuspTrace_tendsto_zero` | ‖Tr_{q,Y} u‖_{L²[-1/2,1/2]} ≤ C_n‖u‖_graph (명시 상수 √max(1+3·drift²,3), 커스프·높이 균일), 그래프 완비화로 확장, Y→∞ 강수렴 0 | **U** (FTC·로그높이 치환·Fubini·Möbius Jacobian) |
| 6 | 38191 | `ambientTestPhysicalGaugePeriodizationAt_unconditional` | 열린 담체에 지지된 C_c^∞ 테스트를 Γ(2) 국소유한 Poincaré 합(±I 이중계수 1/2 보정)으로 물리 코어 벡터로 주기화 | **U** |
| 7 | 39313 | `adjoint_graph_mem_of_bounded_cutoff_commutator` | 일반 힐베르트: 유계 컷오프 U,V와 유계 교환자 C ⇒ (V y, U T†y + C†y) ∈ graph T† | U (일반 정리) |
| 8 | 39909 / 40542 | `modularLogMaxHeight_lipschitz` / `intrinsicCuspCutoff_fderiv_hyperbolic_bound` | SL(2,ℤ)-궤도 최대높이의 log가 쌍곡거리 1-Lipschitz; 내재 컷오프의 y·‖Df‖ ≤ 2K (N 무관) | **U** |
| 9 | 42070 / 42075 | `raisingInvariantCutoffGraphControlAt_unconditional` / lowering | 최대수반 그래프의 콤팩트 지지 국소화(실제 `AdjointCutoffExhaustion` 인스턴스 42015/42043) | **U** |
| 10 | 43903 / 46160 | `friedrichsJointAffineCoordinates_tendsto` / `IsPlanarAffineWeakGraph.friedrichs_identity` | ContDiffBump 정규화 몰리파이어 하나로 기저·상승·하강 좌표 동시 L² 수렴; 약 아핀 Maass 그래프의 정확한 Friedrichs 항등식 P(ρ_j*u)=ρ_j*Pu + (D(t.im ρ_j))*u | U (후자는 약해 정의 입력) |
| 11 | 45102 / 45391 | `mem_weightedWeakSubmodule_iff_maximalAdjointGraphs` / `denseRange_smoothCoreMap_iff_surjective_comparison` | 독립 정의된 약 Sobolev 공간 = 두 최대수반 그래프의 교집합; 코어 조밀성 ⇔ 최소→최대 등거리사상 전사 | U |
| 12 | 45645 | `hasSequentialIntrinsicJointLocalizationAt_unconditional` | 하나의 컷오프 지표로 세 좌표 동시 국소화 | U |
| 13 | 47132 | `ActualModularEndpoint.modularAssociatedOperator_isSelfAdjoint` | 판별식 퍼텐셜 약 Schrödinger 형식 `E_n − t·J_{VΔ}`가 표현하는 Petersson 비유계 연산자는 모든 n, 모든 실수 t에 대해 자기수반 (일반 제1표현정리 46886 + 실제 형식의 Hermitian성 46973·강압성 47034) | **U** (헤더 항목 8 "closed realization/resolvent"의 실질 방출) |
| 14 | 37579 | `strongCrossAdjointAt_of_periodization_cutoff_Friedrichs` | 강한 교차수반 등식 `closedRaise n = (-L)†` 등 | C(Friedrichs 정칙화) → 범위 밖 63072 `strongCrossAdjointAt_unconditional`에서 방출(본인 미검증) |
| 15 | 44695 등 | `weakSchrodinger_solvable_iff_adjointKernel_orthogonal`, `canonicalWeakSolution_*` | 실제 PDE의 Fredholm 대안 | C(`hcompact`) → 범위 밖 55813 `graphPotentialOperator_isCompact_unconditional`에서 방출(본인 미검증) |
| 16 | 45910 / 47354 | `isCompactOperator_of_finite_torus_chart_decomposition` / `twoTorus_isCompactOperator_of_quantitativeTail` | 추상 Fourier–Rellich: 연산자노름 꼬리 소멸 ⇒ 콤팩트 | C(정량 꼬리 추정, 정의상 결론 미포함) — 52691 이후에서 사용 |

## 4. 조건부 인증 감사 (범위 내 모든 명명 가설/인터페이스)

| 가설/구조 | 정의 행 | 분류 | 근거 |
|---|---|---|---|
| `IsGammaTwoInvariantFlux X Y` | 16274 | SUBSTANTIVE(정의적) | 1-형식의 Γ(2) 당김 불변성. 결론(경계합 0)과 다른 국소 항등식; 짝변 소거는 실제 미분·변수변환으로 증명 |
| `HasZeroThreeCuspTail` | 16289 | DISCHARGED | 몫-콤팩트 지지에서 유도(이전 범위 `gammaTwoQuotientCompactFluxTailTightness`; 스칼라판 33767) |
| `GammaTwoPairedPolygonFluxStokes` | 16363 | **DISCHARGED** 33349 | 위 #1 |
| `GammaTwoCompactFluxStokes` | 16376 | DISCHARGED 33376 | |
| `PhysicalGreenIdentityAt` | 25478 | DISCHARGED 33397 | |
| `CoreGraphTraceEstimate`, `UniformSelectedCuspCoreGraphTraceEstimate` | 36474, 36480 | DISCHARGED 36487, 36494 | 추상 패키지는 대체 상수용 API로 잔존 |
| `RaisingMaximalAdjointSequentialApproximationAt` (+Lowering) | 31438/31444 | SUBSTANTIVE ⇔ `StrongCrossAdjointAt`(31474에서 동치 증명) | 범위 밖 63072에서 방출 |
| `AmbientTestPhysicalGaugePeriodizationAt` | 37053 | **DISCHARGED** 38191 | 실제 Poincaré 급수 |
| `RaisingMaximalAdjointWeakMaassIdentificationAt` (+Lowering) | 37297/37303 | DISCHARGED 38208/38213 | |
| `RaisingInvariantCutoffGraphControlAt` (+Lowering) | 37472/37477 | **DISCHARGED** 42070/42075 | |
| `RaisingCompactFriedrichsPeriodizationAt` (+Lowering) | 37485/37490 | SUBSTANTIVE (범위 내 미방출) | 42528에서 ambient Friedrichs 근사로 환원; 범위 밖 62930/62999에서 `_unconditional` 존재 |
| `AdjointCutoffExhaustion` (구조체, Prop 필드 포함) | 39368 | 인스턴스 = **실제 객체**(42015, 42043: 내재 컷오프·실제 교환자) | 퇴화 인스턴스 아님 |
| `hApprox` (ambient 근사열 존재) | 42530, 42553, 44058 | SUBSTANTIVE | 유클리드 Friedrichs 정리의 정확한 형태; 비순환 |
| `hcompact : IsCompactOperator (graphPotentialOperator n)` | 44666– | SUBSTANTIVE | 범위 밖 55813에서 방출(하드 스테이지 근사 + Rellich) |
| `JointGraphCoreDensityAt` | 45306 | SUBSTANTIVE | 범위 밖 49590(강교차수반에서 유도), 63118 |
| `hLower/hRaise : StrongCrossAdjointAt` (45117) | — | SUBSTANTIVE | 위와 동일 |
| `HasVanishingFiniteModeTail`, `HasQuantitativeFiniteModeTail` | 45784, 47318 | SUBSTANTIVE(정량 추정) | "콤팩트"를 필드로 두지 않음 — 주석대로 비순환 |
| `hStage`, `hTail` (46338) | — | SUBSTANTIVE | 55783에서 구체 연산자로 대체 |
| `IsHermitianForm`, `ComplexCoerciveWith` (P9) | 46676 | DISCHARGED (실제 형식: 46973, 47034) | |
| `completedSelectedCuspTraceFamily_*`의 `hCZero : C → 0` | 36764– | 실제로는 충족 불가한 분기(실제 상수는 0으로 가지 않음) — 무해한 여분 API, 과대광고 없음(36601 주석 명시) | |

**결론: 범위 내 CIRCULAR 가설 0건, SUSPECT-VACUOUS 0건.** 열린 의무들은 모두 정리의 결론보다 엄격히 약한 독립 해석적 입력으로 노출되어 있고, 39510 `raising_cutoff_and_Friedrichs_of_sequentialApproximation`이 "경로 Prop들이 목표보다 강하지 않다"는 역방향 정합성까지 증명한다(정직성 측면 모범적). 범위 내 미방출 의무(Friedrichs 정칙화, 퍼텐셜 콤팩트성, 결합 코어 조밀성)는 grep상 범위 밖(49590, 55813, 62930–63121)에서 `_unconditional`로 방출되는 것으로 보이나 그 증명은 본 감사 범위가 아님.

## 5. 정의 충실도

매우 높음. L²: Mathlib `MeasureTheory.Lp`; 테스트함수: Mathlib `TestFunction`(43400); 수반·자기수반·폐포: `LinearPMap.adjoint`/`IsSelfAdjoint`/`IsClosed`; 콤팩트 연산자: `IsCompactOperator`; Fourier 기저: `UnitAddTorus.mFourierBasis`(45830); 부분단위분할: `SmoothPartitionOfUnity`; 몰리파이어: `ContDiffBump.normed`; 합성곱: Mathlib `convolution`; 쌍곡거리: `UpperHalfPlane` metric; 변수변환: `integral_image_eq_integral_abs_det_fderiv_smul` 계열. 약 Sobolev 공간은 완비화가 아닌 분포 결함 범함수의 공통핵으로 독립 정의(44951)하고 최대수반 그래프와의 일치를 증명 — 최소/최대 정의역 혼동을 피한 올바른 설계. 대용(proxy) 정의 없음. 유일한 주의점: `IsPlanarAffineWeakGraph`(44319)는 전평면 ℂ 위 아핀 연산자 `y(σ∂ₓ+∂ᵧ)+c`(y≤0 포함)로 정의되나, 콤팩트 지지(상반평면 내) 대상에만 쓰이므로 문제 없음.

## 6. 실질 수학 비중

- 총 15,800행: 코드 ≈12,230(77%), 주석/독스트링 ≈1,570(10%), 빈 줄 ≈1,321(8%), `#print axioms` 197(1.2%), namespace/open/end 등 ≈482(3%).
- 선언 914개(정리 709, 정리 본문 합 12,766행). 접근자형 5개, 3줄 이하 정리 2개뿐. term-mode 얇은 래퍼(≤12행) 120개 ≈822행(주로 `_unconditional` 재포장, `extendOfNorm_eq` 특수화, 상승/하강 특수화).
- 중복: 상승/하강 평행 사본(이름에 lower 포함 정리 88개 ≈1,700행)과, 내재 컷오프(40000–42092)로 대체된 고정단계 `upstairsCuspCutoff` 블록(38304–39306 ≈1,000행; 일반정리 39313/39368만 재사용).
- **추정: 진짜 수학(비자명 해석·기하·작용소론 증명) ≈ 코드의 75–80%, 즉 전체 행의 ≈60–65%. 스캐폴딩(래퍼·감사 출력·보일러플레이트) ≈10%, 문서 ≈18%.** 이 프로젝트의 다른 모듈들과 비교해 예외적으로 높다.

## 7. 수학적 정확성 / 과대광고

- 잘못된 진술 발견 없음. 부호·계수(예: 37147 "계수 p+1, not p+2", 45953 "transpose 계수 c−1") 처리를 증명으로 고정.
- 문서 부정확(경미): 46443–46447 "P9 source fragment. This file is merged into `Mock2_FunctionalAnalysis_Integrated.lean` … It is source design, not a build report." — 실제로는 본 파일 안에 있고 Integrated는 13행 import 브리지이므로 낡은 주석.
- 명칭 대비 내용(경미): P5.1/P5.4 "Rellich"는 추상 Fourier 꼬리 ⇒ 콤팩트 틀만 담고 H¹ 노름에서 꼬리 추정 유도는 범위 밖(52691~)에 있음. 섹션 주석이 이를 명시하므로 과대광고는 아님.
- `_unconditional` 명칭들은 실제로 가설 없음(확인함). 다만 33389–33472의 11개는 1–3줄 재포장이라 "정리 수" 부풀림 효과가 있음.

## 8. 코드 품질

- 장점: 실제 Mathlib API를 깊이 사용, 대표원 선택 없이 L² 수준에서 논증(예: 41881 `LpToLpRestrictCLM`+조밀 귀납), 일반 정리와 특수화를 분리.
- 단점: (1) 완전 한정 이름 `Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseClosedOperators.PhysicalLocalL2.…`이 네임스페이스를 연 상태에서도 수백 회 반복(36984–37290, 38288–38460, 42125–42572 등) — 가독성 심각 저하. (2) 상승/하강 사본 중복, 대체된 컷오프 블록 잔존. (3) 같은 네임스페이스 반복 재개방(`FixedPhaseNormalizedFriedrichs` 6회, `FixedPhaseIntrinsicAdjointCutoff` 5회) + 매번 `AxiomAudit…` 블록 — "P3.x 패치 누적"의 흔적. (4) `set_option backward.isDefEq.respectTransparency false in`(31554, 31591, 31606) 비표준 옵션 — 건전성 무관하나 취약. (5) 단일 파일 63k행.
- 커스텀 문법/인스턴스(모두 국소·무해): 32030 `local macro_rules`(`(e : GammaTwoActualPolygonEdge).paired` → `GammaTwoActualPolygonEdge.paired e`, 파싱 호환); **40237 `local syntax:max "nhds[" term "]" term:max` + macro_rules `nhds[$s] $x ⇒ nhdsWithin $x $s`** — Mathlib의 `𝓝[s] x`를 ASCII로 재구현한 표기 약어, 인자 순서 정확, 사용처 40321/40331/40387/40406/40416(섹션 40233–40619 국소). 의미론적 위험 없음, 기존 `𝓝[s] x` 표기를 쓰지 않은 불필요한 커스텀화일 뿐; 43393 `local notation "∞" => (⊤ : ℕ∞)`; 44618 `noncomputable local instance actualHMinusOneInnerProductSpace`(강반쌍대에 Riesz 이송 내적, 노름 일치 증명·`toNormedSpace := inferInstance`라 다이아몬드 없음); 44535 `attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup`. `Classical.choose`는 모두 증명된 ∃에서 상수/근방/최대화 행렬 선택(38624, 39805, 40460, 42615, 46296) — 정당.
- Mathlib 업스트림 후보: `LinearPMap.isSelfAdjoint_of_realShift_surjective`(46472), 임베디드 폐형식 제1표현정리 `associatedFormOperator_isSelfAdjoint`(46886, Mathlib에 부재), `adjoint_graph_mem_of_bounded_cutoff_commutator`(39313), `tendsto_zero_of_uniform_bound_of_eventuallyEq_on_denseRange`(41447), `integral_shrinkingKernel_smul_translation_sub_tendsto_zero`(43043), `isEssentialGraphCoreFor_iff_hasSequentialGraphCore`(31410), `hasSequentialGraphCore_of_localization_of_regularization`(36954), `tendsto_zero_normSq_le_energy_Ioi`(34043), `exists_smoothTransition_lipschitz`(40432), `modularLogMaxHeight_lipschitz`(39909), `isCompactOperator_of_vanishingFiniteModeTail`(45804).

## 10. 잠정 점수 (본 범위 한정, 1–10)

- 형식적 건전성: **9** — 탈출구 0, 커스텀 문법·local instance 모두 국소·무해, 컴파일 확인됨(리드).
- 조건부 인증의 정직성(비순환성): **9** — 순환/공허 가설 0, 열린 의무를 정확한 형태로 노출하고 역방향 정합성까지 증명; 1–3줄 `_unconditional` 재포장의 수 부풀림만 감점.
- 수학적 실질성: **9** — 전역 Stokes, 균일 트레이스 정리, Poincaré 주기화, 내재 컷오프, Friedrichs, 제1표현정리 등 연구 수준 해석이 실제 증명됨.
- 정의 충실도: **9** — 전부 Mathlib 실제 개념 사용, 대용 없음.
- 코드 품질·유지보수성: **5** — 완전 한정 이름 남발, 상승/하강·컷오프 중복, 네임스페이스 반복 재개방, 63k행 단일 파일.
- 종합: **8.5** — 이 프로젝트에서 가장 실질적인 구간 중 하나.

---

# 부록: 블록별 상세 메모 (체크포인트 원본)

## 체크포인트 1 (31601–38622 읽음)

### 블록별 메모
- 31518–32544 `GammaTwoNativeEdgeCancellation` (P3.4): 기본 모듈러 타일 세 변(원호/좌·우 수직선)의 ambient 매개화와 실제 도함수(`modularCircularArcAmbient_hasDerivAt` 31557, sqrt 미분), Möbius 합성 변의 `HasDerivAt`(31713, Mathlib `UpperHalfPlane.smulFDeriv`), 변 짝짓기 하 접벡터 호환 `parameterSign_mul_nativePairedTangent_eq_transport`(31818, `UniqueDiffOn` 유일성 이용 — 진짜 증명), 적분 변수변환 `t ↦ -t`(32035), 유한 경계합 소거 `sum_nativeOrientedActualEdgeContribution_eq_zero`(32180). 가정은 `IsGammaTwoInvariantFlux X Y`(16274 정의: 1-형식의 Γ(2) 당김 불변성) — 정의적 성질, 비순환. (U/C-substantive)
  - 32030 `local macro_rules`: `(($e : GammaTwoActualPolygonEdge).paired)` 를 `GammaTwoActualPolygonEdge.paired ($e : …)` 로 바꾸는 순수 파싱 호환용(일반화 field notation on type ascription). 의미론에 영향 없음, 무해.
- 32556–33008 `GammaTwoGlobalStokesBridge` (P3.8): 반열린/열린/닫힌 타일 a.e. 동치(`modularBoundary_null` 이용), `HasZeroThreeCuspTail` → 6개 선택 커스프 차트 공통 높이(32631), 고높이 꼬리에서 Piola 장 국소 0 ⇒ 발산 0, 상단 호로사이클 적분 정확히 0(32905, 32935). 진짜 증명(U).
- 33019–33325 `GammaTwoGlobalStokesCompositionSupport` (P3.9): Mathlib `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` 로 적분가능성 이송(33032), 원래 `hInt` 하나에서 각 타일 절단 적분가능성 도출(33135), 6타일 합으로 환원(33237). (U)
- 33327–33499 (P3.10) **핵심 방출(DISCHARGED)**: `gammaTwoPairedPolygonFluxStokes : GammaTwoPairedPolygonFluxStokes`(33349) — 16363에서 가정으로 쓰이던 Prop(6타일 Γ(2) 기본영역 위 발산정리 = 0)을 실제로 증명. 이어 `gammaTwoCompactFluxStokes`(33376), `physicalGreenIdentityAt_unconditional`(33397), `physicalRaise_isFormalAdjoint_negativeLower_unconditional`(33441), `graphSobolevGreenDefect_eq_zero_unconditional`(33463) 등. 진정한 무조건 Green 항등식(U). 단 `_unconditional` 대부분은 1줄 재포장.
- 31384–31494 `FixedPhaseEssentialCoreAudit`(내 범위 직전, 맥락용): `isEssentialGraphCoreFor_iff_hasSequentialGraphCore` 일반 힐베르트 공간 정리(U, 소박). `RaisingMaximalAdjointSequentialApproximationAt` 등 = 열린 해석적 의무(Friedrichs/Gaffney)로 정직하게 노출.
- 33521–36882 `FixedPhaseHorocycleTrace` (P3.5) **대형 진짜 해석**: 선택 커스프 호로사이클 L² 트레이스.
  - 표적 공간 `SelectedHorocycleL2 := Lp ℂ 2 (volume.restrict [-1/2,1/2])`(33545) — Mathlib 실제 Lp. 가중치 `selectedCuspTraceWeightSq`(33573) = 섬유 스케일/높이.
  - 1차원 FTC 추정(`compactSupport_height_mul_normSq_le_energy_Ioi` 33927, `tendsto_zero_normSq_le_energy_Ioi` 34043: `integral_Ioi_of_hasDerivAt_of_tendsto'`), 로그높이 치환, 단위 당김(`selectedCosetUnitaryPullback` 34539)과 등각 스케일 = |det Df|^{1/2}(36161 `norm_selectedCosetConformalScaleC_sq_eq_abs_det`), Fubini(35460, `integral_prod`), 지수 치환(35833 `integral_comp_mul_deriv_Ioi`), Möbius Jacobian 변수변환(36242).
  - 결과: `coreGraphTraceEstimate_unconditional`(36457) ‖Tr u‖ ≤ C_n ‖coreMap u‖, 상수 `selectedCuspTraceConstant n = sqrt(max(1+3·drift², 3))` 명시. `completedSelectedCuspTrace`(36553, `extendOfNorm`)로 그래프 완비화에 연속확장, `unconditionalCompletedSelectedCuspTrace_tendsto_zero`(36712) 강수렴(3ε 논증). 모두 (U), 실질적이고 업스트림 가치 있는 1차원 보조정리 포함(34043, 34099).
  - 정직성: `CoreGraphTraceEstimate`/`UniformSelectedCuspCoreGraphTraceEstimate`(36474/36480)는 Prop 정의지만 즉시 방출(36487, 36494). `completedSelectedCuspTraceFamily_*`(36745–36799)는 `hCZero : C → 0` 가정 하의 일반 정리 — 실제 상수는 0으로 가지 않으므로 이 분기는 실사용 불가(무해한 여분 API, 과대광고 아님: 주석이 "need not tend to zero" 명시 36601).
- 36884–37613 `FixedPhaseEssentialCoreRoute` (P3.11): 일반 합성정리 `hasSequentialGraphCore_of_localization_of_regularization`(36954, 폐포 논증, U). 구체적 의무 Prop 정의:
  - `AmbientTestPhysicalGaugePeriodizationAt`(37053) → **DISCHARGED** `ambientTestPhysicalGaugePeriodizationAt_unconditional`(38191): Γ(2) 국소유한 Poincaré 합(`gammaTwoPoincarePeriodization` 37929, 중심원소 ±1 이중계수 1/2 보정, `gammaTwo_eq_one_or_centralNegOne_of_effective_eq_one` 37697, `realSmooth_finsum_of_locallyFinite_support` 37893, 공변성 37961/38001, 열린 담체 위 seed 복원 38152). 진짜 구성(U), 퇴화 아님.
  - `RaisingMaximalAdjointWeakMaassIdentificationAt`(37297) → DISCHARGED(38208, 38213).
  - `RaisingInvariantCutoffGraphControlAt`(37472), `RaisingCompactFriedrichsPeriodizationAt`(37485) 및 lowering 짝: SUBSTANTIVE 열린 의무(최대정의역 국소화/Friedrichs 정칙화). `strongCrossAdjointAt_of_periodization_cutoff_Friedrichs`(37579)는 (C). 이후 범위에서 방출되는지 추적 필요.
- 38231~ `FixedPhaseAdjointCutoffCore` (P3.12): `l2Coordinate_hasCompactCarrierSupport`(38276, U), 컷오프 곱 연산자 `peterssonCuspCutoff`(38368, extendOfNorm, ‖·‖≤1), 자기수반(38459), 항등으로 강수렴(38490). (U)

### 잠정 관찰
- 이 구간은 지금까지 거의 전부 실질 해석/기하 증명. 순환 가설 없음. 문자열 레지스트리·원장 없음. `#print axioms` 블록(각 네임스페이스 끝 5–16줄)만 보일러플레이트.

## 체크포인트 2 (38622–42617 읽음)

- 38622–39561 `FixedPhaseAdjointCutoffCore` 계속: 고정단계 교환자 계수(`raiseCuspEuclideanCommutatorCoefficient` 38545)의 담체 위 유한 상계(`exists_closedCarrier_norm_bound_of_quotientCompact` 38594; `Classical.choose`로 상수 선택 38623 — 증명된 ∃에서 선택, 정당). 유계 교환자 연산자의 완비화 확장(38799, 38816), 부호 붙은 교환자 항등식(39091, 39151). **일반 정리 `adjoint_graph_mem_of_bounded_cutoff_commutator`(39313)**: 유계 컷오프 U,V와 유계 교환자 C가 있으면 (V y, U(T†y)+C†y) ∈ graph T† — 일반 힐베르트 공간 결과, 진짜(U), 업스트림 후보. `AdjointCutoffExhaustion` 구조체(39368): 순수 데이터+증명 필드(가정 인터페이스) → `hasSequentialGraphLocalization`(39393). 이 구조체는 42015/42043에서 **실제 객체로 인스턴스화**(퇴화 아님).
  - `raising_cutoff_and_Friedrichs_of_sequentialApproximation`(39510): 역방향 정합성 검사 — 경로 Prop들이 목표보다 강하지 않음을 증명. 정직성 측면 긍정적.
- 39586–39780 `FixedPhaseGoodCuspCutoffBridge`: 상승/하강 교환자가 서로의 정확한 힐베르트 수반임(39694) — 무조건 Green 항등식 사용. (U)
- 39782–40217 내재적 모듈러 최대높이: `modularMaxHeight`(39808, Mathlib `ModularGroup.exists_max_im` + `Classical.choose`), SL(2,ℤ)-불변(39824), **log 최대높이 1-Lipschitz**(39909, `UpperHalfPlane.dist_log_im_le`), 높이>1에서 국소적으로 한 차트의 높이와 일치(39933). 내재적 컷오프 `intrinsicCuspCutoffReal`(40013), 몫 위 콤팩트 지지(40167). 우아하고 진짜(U).
- **40237 `local syntax:max "nhds[" term "]" term:max : term` + `macro_rules | nhds[$s] $x => nhdsWithin $x $s`**: Mathlib의 `𝓝[s] x` 표기를 ASCII로 흉내 낸 순수 국소 표기 약어. `nhdsWithin x s`로 정확히(인자 순서 올바름) 전개. 사용처 40321, 40331, 40387, 40406, 40416뿐. 섹션 `FixedPhaseIntrinsicAdjointCutoff`(40233–40619) 국소. 건전성 영향 없음(무해). 단, Mathlib 기존 표기 `𝓝[s] x`를 쓰지 않은 불필요한 커스텀 문법 — 스타일상 감점 요소.
- 40219–40619: 내재적 컷오프 실매끄러움(40356, 해석적 Möbius 차트 `ContDiffOn.restrict_scalars` + 국소 일치), `smoothTransition` 전역 Lipschitz(40432, 콤팩트 [0,1] + projIcc), 쌍곡거리–유클리드 비교(40500), **N과 무관한 미분 상계** `intrinsicCuspCutoff_fderiv_hyperbolic_bound`(40542, `norm_fderiv_le_of_lip'`). (U, 진짜)
- 40632–41517: 내재적 컷오프 곱 연산자, 자기수반, 항등 강수렴; 교환자 계수 균일상계 4K(41040, 41074); 일반 보조정리 `tendsto_zero_of_uniform_bound_of_eventuallyEq_on_denseRange`(41447, 업스트림 후보); 교환자 강수렴 0(41481, 41493). (U)
- 41519–41857: 내재적 교환자 수반 관계(41622), 부호 그래프 항등식. (U)
- 41859–42092: `completedGaugeMultiplier_hasCompactCarrierSupport`(41881, `LpToLpRestrictCLM` + 조밀성 귀납, 대표원 선택 없이 — 깔끔). **`intrinsicRaisingAdjointCutoffExhaustion`(42015) / `intrinsicLoweringAdjointCutoffExhaustion`(42043): `AdjointCutoffExhaustion`의 실제 인스턴스** → **DISCHARGED `raisingInvariantCutoffGraphControlAt_unconditional`(42070), `loweringInvariantCutoffGraphControlAt_unconditional`(42075)**. 즉 P3.11의 세 의무 중 둘(약 Maass 식별, 컷오프 그래프 제어)이 방출됨.
- 42094–42588 (P3.15): 순방향 Maass 연산의 ambient 테스트 묶음(42125, 42136), 주기화가 미분 좌표까지 보존(42303, 42330), **`periodize_ambientRaisingGraphApproximation`(42395)**: ambient Friedrichs 근사열 → 물리 그래프 근사열. `raisingCompactFriedrichsPeriodizationAt_of_ambientApproximation`(42528): (C) — 남은 가정 `hApprox`는 "모든 콤팩트 약 그래프 벡터에 대한 ambient 순방향 그래프 근사"(유클리드 Friedrichs 정리), SUBSTANTIVE·비순환. 이후 범위에서 방출 여부 추적.

## 체크포인트 3 (42617–45972 읽음)

- 42590–42822 (P3.16) 축약 몫 차트: 고유 불연속성에서 콤팩트 근방 선택(`Classical.choose`, 42614 — 증명된 ∃), 차트-이동 교차 ⇒ 안정자(42659), Mathlib `SmoothPartitionOfUnity.exists_isSubordinate`로 부분단위분할(42729). (U, 진짜 미분기하)
- 42824–43123 (P3.17–18): 평면 L² 평행이동 강연속성(42852, Mathlib `DomAddAct`), 아핀 Maass 교환자의 정확한 항등식(42917: 계수 오차 = t.im·D f(w−t)), 평균 0·L¹유계·축소지지 핵의 강수렴 0(43043). (U) 교과서적 Friedrichs 보조정리를 Bochner L²-값 적분으로 깔끔히 형식화 — 업스트림 후보.
- 43125–43925 (P3.19–21): 실제 `ContDiffBump` 정규화 몰리파이어(43151, rIn=1,rOut=2, `normed`), 질량1·L¹=1·지지반경 2/(j+1)(43284, 43309, 43325); 아핀 교환자 핵을 `TestFunction`으로 묶음(43501), 평균0(43618)·L¹ 불변(43643)·지지(43672); 몰리파이어 작용 → 항등(43831), 교환자 작용 → 0(43875), **공통 지표의 동시 수렴 `friedrichsJointAffineCoordinates_tendsto`(43903)**. (U) 43393 `local notation "∞" => (⊤ : ℕ∞)`: `TestFunction`의 매끄러움 차수용 국소 표기, 무해.
- 43927–44096 (P3.22): 하나의 ambient 열로 결합 그래프(상승+하강) 근사를 주기화(43949). `hasSequentialJointGraphRegularization_of_ambientApproximation`(44055): (C), 가정 = ambient 근사열 존재(유클리드 Friedrichs) — SUBSTANTIVE.
- 44098–44506 (P3.23–24): 몰리파이 대표원 C^∞(44138, Mathlib `contDiff_convolution_left`), 교환자 핵 = D(t.im ρ_j) 정확 증명(44228), 평면 약 아핀 그래프 Prop `IsPlanarAffineWeakGraph`(44319) — 정의(약해 개념), 가정 아님. (U)
- 44508–44790 (P6/P7 브리지) `ActualScalarDiscriminantPDE`: 실제 약 Schrödinger 연산자 `weakSchrodingerOperator n t = E_n − t·J_{VΔ}`(44559), 코어 위 공식(44577). **`noncomputable local instance actualHMinusOneInnerProductSpace`(44618)**: 강반쌍대에 Riesz 이송 내적 부여 — 기존 노름과 일치함을 증명(`norm_sq_eq_re_inner`), `toNormedSpace := inferInstance`이므로 위상 다이아몬드 없음. 정당하나 local instance로 구조를 주입하는 패턴은 주의 대상(국소라 위험 제한적). `attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup`(44535) 우선순위 조작 — 무해.
  - Fredholm 결과(44664–44758) 전부 **(C) `hcompact : IsCompactOperator (graphPotentialOperator n)`** 가정. 정직하게 "P5가 증명할 것"으로 표기. SUBSTANTIVE(판별식 퍼텐셜의 콤팩트성 — 비순환, 실제로 참일 개연성 높음; 판별식 Δ의 커스프 감쇠). 내 범위 안에서 방출되는지 추적 → (아래 확인).
- 44792–45445 (P4.1) `IndependentWeightedWeakSobolev`: 약 Sobolev 공간을 완비화가 아니라 **연속 결함 범함수들의 공통핵으로 독립 정의**(44951) — 최소/최대 정의역 비교를 위한 올바른 설계. 최대수반 그래프와 정확히 일치(45025, 45067, 45102), 닫힘·완비(45153, 45172), 최소 그래프 완비화 → 약공간 등거리 포함(45354), 치역 닫힘(45384), **조밀성 ⇔ 전사성(45391)**. `JointGraphCoreDensityAt`(45306) = 열린 의무(SUBSTANTIVE, "joint Friedrichs"), `graphCompletionEquivWeightedWeak`(45423)은 (C). (U 대부분)
- 45447–45691 (P4.2): 하나의 내재 컷오프로 세 좌표 동시 국소화(45473), 약공간 보존(45540, 일반 교환자 정리 39313 재사용), 3좌표 동시수렴(45609), **`hasSequentialIntrinsicJointLocalizationAt_unconditional`(45645)** (U).
- 45693–45943 (P5.1) `P5LocalFourierRellich`: 유한 힐베르트 사영 = 랭크1 합 ⇒ 콤팩트(45746), 연산자노름 꼬리 소멸 ⇒ 콤팩트(45804, Mathlib `isCompactOperator_of_tendsto`), 실제 2-토러스 Fourier 기저(45830, `UnitAddTorus.mFourierBasis`), 유한 차트 조립(45910). `HasVanishingFiniteModeTail`(45784)은 정의(결론 아님) — 주석대로 비순환. 다만 "Rellich"라는 이름에 비해 실제 Rellich 내용(꼬리 추정을 H¹ 노름에서 유도)은 아직 없음: 추상 틀(U, 소박).

## 체크포인트 4 (45972–47420 읽음)

- 45945–46243 (P3.25): `fderiv_friedrichsMollifiedRepresentative_apply`(46008, Mathlib `hasFDerivAt_convolution_left`), 몰리파이 = 반사 평행이동 테스트와의 쌍선형 짝(46040), 순방향 테스트와 전치의 차 = 교환자 핵(46125, 계수 c 완전 소거), **`IsPlanarAffineWeakGraph.friedrichs_identity`(46160)**. (U)
- 46245–46382 (P5.2): 판별식 커스프 ε_N=1/(N+1)과 문자 그대로의 커스프 높이(`Classical.choose`, 46296), `graphPotentialOperator_isCompact_of_literalStageFactorization`(46338): (C) hStage·hTail — 범위 밖 55783/55813에서 구체화·방출.
- 46384–46441: 표준 주파수 열거(46392), Parseval 강수렴(46418, 연산자노름 수렴 아님을 주석이 명시). (U)
- 46443–47160 (P9) `P9ClosedFormRealization`: 일반 정리 `LinearPMap.isSelfAdjoint_of_realShift_surjective`(46472, 스펙트럼 정리 없이 직접 증명), 임베디드 질량형식·표현 그래프·연산자(46535–46670), Lax–Milgram 해소(46719), 표현 연산자 실수 이동 전사(46763), 대칭(46787), 정의역 조밀(46815, 해소를 두 번 써서 증명), **제1표현정리 `associatedFormOperator_isSelfAdjoint`(46886)**. 실제 모듈러 끝점: 기저 임베딩 단사(46925, 결합 폐가능성)·조밀(46933), 퍼텐셜 형식 Hermitian(46945, 이중 조밀 귀납), 질량 이동 `|t|·uniformBound`로 강압성 1(47034), **`modularAssociatedOperator_isSelfAdjoint`(47132)**, 닫힘(47144). 전부 (U). 46443–46447의 "merged into Integrated" 주석은 낡음.
- 47162–47294 (P5.3): 실제 3-커스프 단계로의 L² 제한 `graphLiteralStageRestriction`(47210, `LpToLpRestrictCLM`), 대표원(47226, 47237), 축약성(47262). (U)
- 47296–47406 (P5.4): 정량 Fourier 꼬리 ⇒ 연산자노름 꼬리 ⇒ 콤팩트(47326–47393). (U, 소박)

## 커버리지 로그
- 31230–31600: 맥락용 선행 독해(범위 밖).
- 31601–32608, 32608–33607, 33607–34606, 34606–35505, 35505–36405, 36405–37224, 37224–37923, 37923–38622: 정독 (체크포인트 1).
- 38622–39321, 39321–40020, 40020–40670, 40670–41319, 41319–41968, 41968–42617: 정독 (체크포인트 2).
- 42617–43316, 43316–44015, 44015–44714, 44714–45413, 45413–45972: 정독 (체크포인트 3).
- 45972–46671, 46671–47420: 정독 (체크포인트 4). 47407–47420은 다음 범위(P10) 시작부 확인용.
- 스킴: 없음. `#print axioms` 197행은 대상 이름만 확인.
- 범위 밖 grep 확인(증명 미검증): 16270–16420(Prop 정의), 25470–25490, 28060–28140, 49585–49595, 55360–55385, 55780–55820, 62925–62945, 63068–63082.
