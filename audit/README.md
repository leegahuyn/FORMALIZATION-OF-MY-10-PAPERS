# Lean 형식화 평가 보고서 — `PrimalitySheafVerification` (13개 주요 모듈, 약 35만 줄)

- **평가 대상**: `leegahuyn/mathlib4` 태그 `formalization-final-authority-2026-08-21` (HEAD `8f7e861`)의 `PrimalitySheafVerification/`
- **대상 모듈**: Spt1–Spt7, Mock1, Mock1_Advanced, Mock2, Mock2_Advanced, Mock2_FunctionalAnalysis, QYM(= Mock3)
  - `Mock3.lean`은 QYM을 다시 내보내는 12줄짜리 브리지입니다.
  - `Mock2_FunctionalAnalysis_Integrated.lean`은 13줄짜리 브리지입니다.
- **규모**: 13개 모듈 합계 **352,735줄**(약 16 MB)
  - 정리·보조정리 20,989개, def 6,957개, abbrev 772개, structure 1,144개, instance 243개, inductive 163개
- **평가 일자**: 2026-10-03
- **평가 방식**: 리드 감사자(Claude)가 기계 검증을 직접 수행했습니다. 그와 별도로 모듈별·구간별 에이전트 13개 이상이 전체 줄 범위를 나눠 정독했습니다.

> 이 문서가 최종 보고서입니다. 모듈별 상세 보고서는 [`modules/`](modules/)에, 재현 가능한 검증 스크립트와 로그는 [`verification/`](verification/)에 있습니다.

---

## 0. 한눈에 보는 결론

| 평가 축 | 점수 (10점 만점) | 한 줄 요약 |
|---|---|---|
| **형식적 건전성 (기계 검증)** | **9.5** | 35만 줄 전체가 오류 0으로 컴파일됩니다. 상수 68,681개 전부 표준 3공리만 씁니다. Mathlib는 변조되지 않았습니다. |
| **조건부 인증의 정직성 (비순환성)** | **약 5** (줄 가중 5.3 / 모듈 평균 4.7) | 일부는 모범적입니다(FA·QYM·Mock2_Advanced). 반면 "가설 = 결론"인 정리, 만족 불가능한 가설, 퇴화한 예시 인스턴스가 광범위합니다. |
| **수학적 실질성** | **약 5** (줄 가중 4.7 / 모듈 평균 5.1) | 실질 수학은 전체 줄의 **약 26%**(추정 9만 줄)입니다. 그중 Mock2_FunctionalAnalysis는 연구 수준입니다. |
| **정의 충실도** | **약 5.3** | Tor, Γ(2), η, Weierstrass, ℚ_p 로그는 Mathlib의 실제 대상입니다. 반면 층·모티브·étale·mock theta 계수 공식 쪽은 대용물(프록시)이 많습니다. |
| **코드 품질·유지보수성** | **약 4** | 최대 9만 줄짜리 단일 파일입니다. 같은 Tor 계산이 5개 모듈에 중복되어 있고, 문자열 원장과 `#print axioms` 수천 줄이 있습니다. 워크플로 파일은 1,015개입니다. |
| **종합** | **약 5 / 10** | 기계 검증된 정리 저장소로서는 신뢰할 수 있습니다. 그러나 논문 주장의 조건부 인증으로서 의미 있는 부분은 절반에 못 미칩니다. |

**핵심 메시지**

1. **"컴파일된다"는 점은 의심할 여지가 없습니다.** 13개 모듈, 브리지 2개, `BuildAll`을 로컬에서 Mathlib부터 소스 빌드했고, 모두 exit 0, 오류 0, `sorry` 경고 0이었습니다. 상수 68,681개 전수 공리 감사에서도 비표준 공리 의존은 0건이었습니다. 감사 도구가 오염을 실제로 잡아내는지는 `sorry` 카나리아로 확인했습니다.
2. **"컴파일된다"가 곧 "논문 주장이 증명되었다"는 뜻은 아닙니다.** 논문의 헤드라인 주장은 어느 것도 Lean에서 증명되지 않았습니다. 해당 주장은 다음과 같습니다.
   - 소수성 층 Theorem 1/18
   - 5-검출기 Master Equivalence
   - "RH ⟺ TP"
   - mock theta 정확 계수 공식
   - Kuznetsov 경유 결론
   - 질량간극

   이 주장들은 다음 셋 중 하나로만 들어와 있습니다.
   - 결론을 그대로 가정에 넣은 "조건부" 정리
   - 만족할 수 없는 인터페이스 위의 공허한 정리
   - 0이나 자명한 데이터로 채운 예시 인스턴스
3. **진짜 성과도 분명합니다.** 대표적인 것은 다음과 같습니다.
   - Mathlib의 유도함자 `Tor`를 명시적 사영분해로 계산한 `Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N)`
   - η 변환법칙, Γ(2) 기본영역, Fredholm 대안, Rellich 콤팩트성
   - 일반 Hilbert 공간의 T†† = closure(T)

   일부는 Mathlib에 기여할 만한 수준입니다. 또 논문의 오류를 Lean 정리로 반증·정정한 사례가 20건 이상 있는데, 이는 형식화의 본래 가치를 잘 보여 줍니다.

---

## 1. 평가 방법

| 단계 | 내용 | 수행 |
|---|---|---|
| 기반 확인 | 포크의 `Mathlib/` 트리 해시와 `lake-manifest.json`을 상류 저장소와 대조했습니다. 상류 커밋 **`93594942`**(2026-08-03, `v4.33.0-rc1`)와 **완전히 일치**합니다. 포크는 파일을 추가만 했고, 기존 파일은 `.github/workflows/pre-commit.yml` 1건만 수정했습니다. | 리드 |
| 정적 전수 스캔 | 주석과 문자열을 제거한 뒤 13개 모듈 전체를 토큰 단위로 스캔하고, 선언 30,446개를 분류했습니다. 스크립트: [`verification/lean_scan.py`](verification/lean_scan.py) | 리드 |
| 실제 컴파일 | Mathlib 캐시 서버가 막혀 있어 **Mathlib 전체(8,696개 작업)를 소스에서 빌드**했습니다. 이어서 각 모듈을 `lake env lean -DmaxErrors=2000`으로 컴파일했습니다. 스크립트: [`verification/build_psv.sh`](verification/build_psv.sh) | 리드 |
| 공리 전수 감사 | `PrimalitySheafVerification.*`의 모든 상수에 대해 전이적 공리 의존성을 메모이즈된 DFS로 계산했습니다. 검증 파일: [`verification/AxiomAudit.lean`](verification/AxiomAudit.lean) | 리드 |
| 반증 검증 | Spt7 인터페이스가 만족 불가능함을 Lean으로 증명했습니다: [`verification/Spt7Vacuity.lean`](verification/Spt7Vacuity.lean) | 리드 |
| 정독 | 13개 모듈을 에이전트에 하나씩 배정했습니다. 사용량 한도로 중단된 대형 파일은 구간을 나눠 새 에이전트가 이어 읽었습니다. 같은 루브릭으로 평가했고, 읽은 범위 로그는 각 보고서 끝에 있습니다. | 에이전트 |
| 교차 검증 | 에이전트 주장 가운데 핵심 사실은 리드가 원문 재확인, grep, Python 수치 계산으로 다시 확인했습니다(§8). | 리드 |

---

## 2. 기계 검증 결과 (확정 사실)

### 2.1 컴파일 (로컬, Mathlib 소스 빌드 후)

출처: [`verification/build_status.txt`](verification/build_status.txt). 환경은 4코어 / 15 GB입니다.

| 모듈 | exit | 오류 | 경고 | `sorry` 경고 | 시간(초) |
|---|---|---|---|---|---|
| Spt1 | 0 | 0 | 20 | 0 | 134 |
| Spt2 | 0 | 0 | 39 | 0 | 137 |
| Spt3 | 0 | 0 | 28 | 0 | 116 |
| Spt4 | 0 | 0 | 27 | 0 | 115 |
| Spt5 | 0 | 0 | 26 | 0 | 119 |
| Spt6 | 0 | 0 | 23 | 0 | 54 |
| Spt7 | 0 | 0 | 18 | 0 | 106 |
| Mock1 | 0 | 0 | 66 | 0 | 60 |
| Mock1_Advanced | 0 | 0 | 112 | 0 | 590 |
| Mock2 | 0 | 0 | 341 | 0 | 194 |
| Mock2_Advanced | 0 | 0 | 786 | 0 | 442 |
| Mock2_FunctionalAnalysis | 0 | 0 | 466 | 0 | 771 |
| Mock2_FunctionalAnalysis_Integrated | 0 | 0 | 0 | 0 | 7 |
| QYM | 0 | 0 | 345 | 0 | 1178 |
| Mock3 | 0 | 0 | 0 | 0 | 7 |
| BuildAll (13개 + 브리지) | 0 | 0 | 0 | 0 | 10 |

- 경고는 총 2,297개입니다. 대부분 deprecated 이름, 사용하지 않는 변수, 린터 경고입니다.
- 저장소에 남아 있는 과거 CI 기록은 Mock2_FunctionalAnalysis가 실패한 상태였습니다(2026-08-16 시점 오류 4개). 그러나 **현재 소스는 깨끗하게 컴파일됩니다.**
- 저장소 안에는 "13개 파일 15/15 최종 PASS" 기록이 없었습니다. 이번 로컬 빌드가 그 공백을 메웁니다.

### 2.2 공리 전수 감사

```
PSV constants audited: 68681; tainted by non-standard axioms: 0; by axiom: []
canary: some (some (sorryAx)); control Nat.add_comm: some (none)
```

- `PrimalitySheafVerification.*`에 정의된 상수(보조 상수 포함) **68,681개 전부**가 `propext`, `Classical.choice`, `Quot.sound`만 씁니다.
- 일부러 `sorry`로 만든 카나리아 정리는 `sorryAx` 오염으로 정확히 잡혔습니다. 따라서 감사 도구 자체가 유효합니다.

### 2.3 탈출구 정적 스캔 (주석·문자열 제거 후)

| 항목 | 13개 모듈 합계 |
|---|---|
| `sorry` / `admit` | 0 / 0 |
| `axiom` / `opaque` / `unsafe` / `implemented_by` / `extern` | 0 |
| `native_decide` / `Lean.ofReduceBool` | 0 |
| `set_option maxHeartbeats` 상향 | 22곳 (최대 8,000,000, QYM 49552행. 한 줄짜리 정리에 걸려 있어 건전성 문제는 없음) |
| 사용자 정의 `elab` | Spt3·Spt5의 "axiom firewall" 4개. `collectAxioms` 기반의 정당한 검사입니다. 다만 검사 대상이 일부 선언으로 한정됩니다. |

### 2.4 Mathlib 무결성

포크의 `Mathlib/` 디렉터리는 상류 `93594942`와 git 트리 해시가 같습니다(`a8a691df…`). `lean-toolchain`과 `lake-manifest.json`도 이 커밋과 일치합니다. **Mathlib를 고쳐서 증명을 통과시킨 흔적은 없습니다.**

> **주의 — 컴파일 성공의 의미**: Lean 커널은 "주어진 진술이 주어진 가정에서 따라 나온다"만 보장합니다. 진술이 논문의 의미를 충실히 담는지, 가정이 결론 자체이거나 거짓은 아닌지는 보장하지 않습니다. §4 이하가 바로 그 부분을 평가합니다.

---

## 3. 모듈별 평가

건전성 열은 리드가 확인한 컴파일·공리 결과를 반영해 모두 9로 맞췄습니다. 에이전트가 처음에 "컴파일 미확인"으로 7–8점을 주었는데, 이번 검증으로 그 감점 사유가 해소되었기 때문입니다. 나머지 축은 에이전트 평가를 그대로 쓰되, 구간별로 나눠 읽은 대형 모듈은 리드가 구간 점수를 종합했습니다.

| 모듈 | 줄 수 | 건전성 | 정직성 | 실질성 | 충실도 | 품질 | **종합** | 실질 수학 비율(추정) | 상세 |
|---|---:|---|---|---|---|---|---|---|---|
| Spt1 | 8,087 | 9 | 5 | 6 | 6 | 5 | **6** | 30–35% | [보고서](modules/Spt1.md) |
| Spt2 | 8,878 | 9 | 3 | 5 | 4 | 5 | **5** | 20–25% | [보고서](modules/Spt2.md) |
| Spt3 | 7,506 | 9 | 4 | 6 | 6 | 4 | **5.5** | 코드의 약 35% | [보고서](modules/Spt3.md) |
| Spt4 | 8,714 | 9 | 3 | 4 | 3 | 4 | **4** | 약 20% | [보고서](modules/Spt4.md) |
| Spt5 | 8,071 | 9 | 4 | 6 | 5 | 4 | **5.5** | 약 17% (코드의 35%) | [보고서](modules/Spt5.md) |
| Spt6 | 8,651 | 9 | 3 | 6 | 6 | 3 | **5** | 약 33% | [보고서](modules/Spt6.md) |
| Spt7 | 18,114 | 9 | 3 | 5 | 5 | 3 | **4** | 약 25% | [보고서](modules/Spt7.md) |
| Mock1 | 9,831 | 9 | 5 | 3 | 5 | 3 | **4** | 13–15% | [보고서](modules/Mock1.md) |
| Mock1_Advanced | 90,615 | 9 | 2.5 | 1.5 | 2.5 | 2 | **2** | 2–3% | [p1](modules/Mock1_Advanced_part1_notes.txt) · [p2](modules/Mock1_Advanced_part2.md) · [p3](modules/Mock1_Advanced_part3.md) · [p4](modules/Mock1_Advanced_part4.md) · [p5](modules/Mock1_Advanced_part5.md) |
| Mock2 | 26,607 | 9 | 6 | 5 | 5 | 4 | **5.5** | 약 22% | [보고서](modules/Mock2.md) |
| Mock2_Advanced | 31,919 | 9 | 6.5 | 6 | 6.5 | 5 | **6.5** | 38–42% | [p1](modules/Mock2_Advanced_part1.md) · [p2+종합](modules/Mock2_Advanced_part2.md) |
| Mock2_FunctionalAnalysis | 63,138 | 9 | 8.5 | 8 | 8.5 | 5 | **8** | 약 55% | [p1](modules/Mock2_FunctionalAnalysis_part1_notes.txt) · [p2](modules/Mock2_FunctionalAnalysis_part2.md) · [p3](modules/Mock2_FunctionalAnalysis_part3.md) · [p4](modules/Mock2_FunctionalAnalysis_part4.md) |
| QYM (Mock3) | 62,604 | 9 | 7 | 5 | 6.5 | 4.5 | **6** | 약 30% | [p1](modules/QYM_part1_notes.txt) · [p2](modules/QYM_part2.md) · [p3](modules/QYM_part3.md) · [p4](modules/QYM_part4.md) |
| **줄 가중 평균** | 352,735 | 9 | 5.3 | 4.7 | — | — | **5.1** | **약 26%** | |

### 모듈별 한 줄 평

- **Spt1**
  - 좋은 점: 유도함자 Tor₁ 계산(5650–5776)과 ℚ_p 로그가 견실합니다.
  - 문제점: "소수성 층" 정리 1(1884)은 산술 동치를 포장한 것입니다. Goldwasser–Kilian(GK) 가정(3082)은 후보 X를 전혀 언급하지 않아 내용이 없습니다.
- **Spt2**
  - 좋은 점: 단변수 étale ⇔ squarefree(1825)와 Ω ≅ A/(f′)(1882)는 진짜 가환대수입니다.
  - 문제점: Master Equivalence는 다섯 버전 모두 순환적입니다(697, 2451).
- **Spt3**
  - 좋은 점: Tor₁ 계산(3372), Pocklington–Lehmer(3647–3881), p진 로그 수렴(4066)이 있습니다.
  - 문제점: `AKSIsComplete`(781)는 가설이 곧 결론입니다. "Theorem 18 무조건"(6072)은 Lucas 판정법을 다시 적은 것입니다.
- **Spt4**
  - 좋은 점: 수렴 p진 로그(5221–5580)가 있습니다.
  - 문제점: étale–motivic–derived 핵심은 순환 인터페이스로만 들어와 있습니다. Tor와 Ext가 같은 타입의 프록시입니다.
- **Spt5**
  - 좋은 점: Tjurina 길이 공식(2723)이 있습니다.
  - 문제점: "UNCONDITIONAL" 검출기 TFAE가 실제로는 Ω 사영성 필드(3136–3146)에 의존하는데, 노드 반례를 바로 이 필드가 배제합니다.
- **Spt6**
  - 좋은 점: `ProjRes.torFullIso`(3294)가 모범적입니다.
  - 문제점: 형식 로그 함수방정식은 주석 처리되어 있습니다(7867–7954). 그런데도 상태 원장은 이를 `.unconditional`로 표기합니다(6351).
- **Spt7**
  - 좋은 점: `abstractTorOneIsoGcd`(14746)와 Jacobi 공식(8503/8619)이 있습니다.
  - 문제점: `ModuleDepthDimensionInterface`(6709)는 **만족 불가능**합니다(리드가 Lean으로 증명). 따라서 `prop18_*` 약 160개가 공허하게 참입니다.
- **Mock1**
  - 좋은 점: 초등 CRT/Tor 코어는 정직합니다.
  - 문제점: Thm I.8 인증서(7548)는 결론을 필드로 가집니다. 해석적 주장은 인스턴스가 하나도 없습니다.
- **Mock1_Advanced**
  - 정리 6,361개 중 57%가 필드 사영입니다.
  - reference 인스턴스는 전부 퇴화했습니다(영함수, modulus 1, Γ(0,4π) := 1).
  - 실물 Ramanujan f(q) 16계수(68301)는 정확하지만, 인증 체인에는 연결되어 있지 않습니다.
- **Mock2**
  - 좋은 점: Mathlib `Tor'` 브리지(5057), η 승수(16327–16685), 논문 반증 4건이 있습니다.
  - 문제점: Prop 17/18 연결은 서로 무관한 두 성분의 곱입니다(19267).
- **Mock2_Advanced**
  - 좋은 점: `fullThetaCovariance`(21156)가 θ 승수 가설을 실제로 해소합니다. Γ(2) 생성원 정리(20785)도 있습니다.
  - 문제점: 원장의 `correctedAndProved` 일부가 퇴화 모델 위에서만 성립합니다.
- **Mock2_FunctionalAnalysis**
  - 이 프로젝트에서 가장 실질적인 모듈입니다. η 변환법칙(4457), Γ(2) 기본영역(6097), T†† = closure(25209), 곡선 타일 Green 정리(29863), Rellich(54809), Fredholm 대안 전체(56355–56543)가 있습니다. 순환 가설은 거의 없습니다.
  - 논문의 최종 산술 결론은 형식화되지 않았고, 파일도 그렇게 스스로 밝힙니다(57088).
- **QYM**
  - 좋은 점: Γ(2)\ℍ의 다양체 구조(46412)와 3-커스프 경계 분해(43286)가 있습니다. 논문 질량간극 추론을 반례 2개로 반박합니다(5510, 30033).
  - 한계: Yang–Mills 질량간극을 **증명하는 정리도 반증하는 정리도 없습니다.** "간극"은 유한차원 장난감(3/4 = 1 − 1/4, `norm_num`)과 사영 연산자 수준에 머뭅니다.

---

## 4. 교차 모듈 핵심 발견

### 4.1 진짜 성과 (무조건, 실제 Mathlib 대상)

| 주제 | 대표 선언 (모듈:행) | 비고 |
|---|---|---|
| Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd(M,N) | Spt1 `tor1_obj_iso` (5650–5776), Spt3 `tor1_obj_iso` (3372), Spt6 `ProjRes.torFullIso` (3294), Spt7 `abstractTorOneIsoGcd` (14746), Mock2 `mathlibTor1ZIsoCyclicModel` (5057) | Mathlib의 범주론적 `Tor`를 명시적 사영분해와 `isoLeftDerivedObj`로 계산합니다. **5중 중복**은 품질 문제입니다. |
| η 변환법칙과 승수 | FA `eta_transform` (4457), Mock2 16327–16685 | Mathlib의 `discriminant`·`ModularForm.eta`를 씁니다. |
| Γ(2) 기하 | FA 기본영역 (6097), M2A 생성원 (20785), QYM free action (37864), 3-커스프 경계 (43286), 다양체 구조 (46412) | |
| 함수해석 | FA I−K의 치역이 닫혀 있음 (3241), `adjoint_adjoint_eq_closure` (25209/25307), 닫힘가능성 (25633, 25703, 26142), Rellich (54809, 55813), Fredholm 대안 (56355–56543), `strongCrossAdjointAt_unconditional` (63072) | 연구 수준입니다. 퍼텐셜 V = y¹²\|Δ\|²는 Mathlib `discriminantCuspForm`으로 정의합니다. |
| 대수·정수론 | Spt2 `formallyEtale_iff_squarefree_of_ne_zero` (1825), `kaehlerEquivJacobianQuotient` (1882), Spt5 Tjurina (2723), Spt3 Pocklington–Lehmer, p진 로그 수렴 (Spt1·3·4), Spt7 det–trace 항등식 (8884) | |
| θ 승수 | M2A `fullThetaCovariance` (21156) | 이전 조건부 정리들(5120–5199)을 무조건으로 바꿉니다. |

### 4.2 문제 A — 순환 가설: 가설이 곧 결론인 "조건부" 정리

- **Spt3** `def AKSIsComplete (FEC) : Prop := ∀ X, X.Prime ↔ FEC X` (781)
  - 이를 쓰는 정리: `prime_iff_section_of_complete … := hFEC X` (785), `theorem18_of_any_complete` (6079), `global_certificate_conditional` (7284)
  - 마지막 정리는 "인증된(certified)" 방화벽 목록에까지 들어 있습니다.
- **Spt2**: `master_equivalence` (697)는 `Hder : der = 0 ↔ smooth`를 가정합니다. 이것은 TFAE의 한 성분 그 자체입니다. `ArithmeticCurve` (2451)는 결론을 필드로 가지며, "논문 정리" 약 45개(2540–2778)가 그 필드의 사영입니다.
- **Spt6** `goodPrime_synchronization` (2528), `Thm93Assembly.thm93_full_tfae` (4129): 가설 `Hsync`·`Hsmooth`·`Hder`가 TFAE의 각 면을 그대로 진술합니다.
- **Spt7** `equivalence_C` (11952), `GlobalEquivalenceCBridge.rh_iff_tp` (12589): "RH"와 "TP"는 임의의 `Prop`이고, 둘 사이의 동치가 필드로 주어집니다.
- **Mock1** `StabilityCertificate.alpha_invariant` (7548): 결론(α 불변)이 필드이고, Thm I.8 (7803)은 그 필드를 `rw`한 것입니다.
- **Spt1** `MtALogInput` (3912)도 가설이 곧 결론입니다.
- **자동 집계**: 이름 붙은 `Prop` 가설을 그대로 적용해서 끝나는 증명이 **191개**, `Prop` 값 `def`가 **1,072개**입니다. 정리 20,989개 중 **4,311개(20.5%)**는 구조체 필드 사영(accessor)입니다.

### 4.3 문제 B — 만족 불가능하거나 거짓인 가설 (공허한 정리)

- **Spt7** `ModuleDepthDimensionInterface` (6709)와 `ENatDepthDimensionAPI` (6775) — **Lean으로 증명했습니다**([`verification/Spt7Vacuity.lean`](verification/Spt7Vacuity.lean)).
  - 영 모듈 `PUnit` 위에서는 모든 리스트가 약정칙열이므로, 이 인터페이스는 `n ≤ depth PUnit`을 모든 n에 대해 요구하게 됩니다. 이것은 모순입니다.
  - `theorem interface_false … (I : ModuleDepthDimensionInterface R) : False`가 고정 Mathlib 위에서 컴파일됩니다.
  - 결과적으로 `prop18_*` 약 160개(6929–8350)가 공허하게 참입니다.
- **Spt3**: `hB : IsSheaf siteJ (const ℕ)`는 거짓입니다(빈 덮개에서 유일성이 깨지며, 파일 스스로 4618행에서 인정합니다). 이를 가정하는 `amalgam_isSheaf` (1226) 등은 공허합니다. 이후 4691행에서 올바른 대체판을 제공합니다.
- **Spt1**: GK 단계 인증서의 어떤 필드도 후보 X를 언급하지 않습니다. 에이전트는 y²=x³−x(q=7)와 F₇ 위 모형 y²=x³+3(13점)으로 만든 단계 인증서에서 가정이 `Nat.Prime 4`를 함의한다고 지적했습니다(Python 점 개수 확인, Lean 구성은 아님). 리드는 F₇ 위 13점을 손으로 재계산해 확인했습니다.
- **Mock1_Advanced**: `…EntropyAsymptoticProofInput` (73588)은 실제 f(q) 계수에 대해 α ∈ [1.81438, 1.81439], β ≈ −0.7597을 요구합니다.
  - 리드가 f(q) 계수 3,000항을 계산해 비교했습니다.
    - 파일 모형의 잔차는 n=3000에서 −29로 **발산**합니다.
    - 참 점근식 α = π/√6, β = −log 2의 잔차는 −0.0005로 수렴합니다.
  - 따라서 이 입력은 실제 객체로 채울 수 없습니다.
- **Spt5**: Ω 사영성 필드(3136–3146)가 "UNCONDITIONAL" 검출기 정리를 노드 반례에서 구조적으로 보호합니다. 즉 숨은 가정입니다.

### 4.4 문제 C — 퇴화한 예시(reference) 인스턴스

- **Mock1_Advanced**
  - `reference…` 422개가 모두 퇴화 데이터입니다. Rademacher·Kloosterman(modulus 1, 값 0)·ξ-연산자·shadow는 영함수입니다(3185–3470).
  - 정확 계수 공식의 인자가 모두 1입니다. "Γ(0,4π)"에 1을 넣었는데(28212), 참값은 E₁(4π) ≈ 2.6×10⁻⁷입니다.
  - `kuznetsovAccepted`·`weilBoundAccepted`·`lValueTheoryAccepted`는 `True`로 채워져 있습니다(67574–67584).
  - 최종 결론 `reference_advanced_claims_ii_microlocal_certification_readiness` (84516)은 이런 퇴화 인증서 약 50개를 조립한 것입니다. 그 안의 `rlf_end_to_end`는 `Fin 0` 위의 진술입니다.
- **Spt6** `exampleSmoothCurve` (8138)는 전부 0입니다.
- **Mock2**: `scalarAnalyticData`의 연산자는 0입니다. `CommonAnnulus` (10093)는 inner < 1 < outer 조건 때문에 실제 mock theta 급수를 **아예 받아들일 수 없습니다**.
- **Mock2_FA**: `constantCompactCuspTail` (21464)는 ε = 0으로 채워집니다. 다만 이 모듈의 최종 정리들은 이런 인스턴스에 의존하지 않습니다.

### 4.5 문제 D — 상태 원장·라벨과 실제 내용의 불일치

- **Spt6**: 형식 로그 함수방정식은 블록 주석 안에 있고(7867–7954), 그 자리에 `formal_log_section_skipped : True := trivial` (7959)이 들어 있습니다. 그런데도 원장은 이를 `.unconditional`로 표기합니다(6351).
- **Spt3**: "Theorem 18 unconditional"(6072)의 진술은 `X.Prime ↔ True ∧ True ∧ True ∧ LucasCert X`입니다. 머리말(131)은 같은 결과를 "조건부"라고 적어서 원장끼리 서로 모순됩니다.
- **Spt1**: "UNCONDITIONAL" 표기가 인스턴스 없는 `[PadicLogTailCertificate p]`에 의존합니다(7083 이하).
- **Spt5**: 독스트링이 y²=x³−x / 𝔽₅를 supersingular라고 적습니다(6562). 같은 파일의 `ecTrace_x3mx_5 = -2`(5564)와 모순되며, 실제로 이 곡선은 ordinary입니다(리드가 재계산: #E(𝔽₅) = 8, a₅ = −2).
- **Mock1_Advanced**: `EnvironmentPinManifest` (12114–12212)는 `leanprover/lean4:v4.31.0`과 Mathlib `fabf563a…`를 필드로 고정합니다. 여기에 존재하지 않는 `outputs/Mock1_Integrated.lean`, `scripts/audit.ps1`까지 적고 `rfl`로 "인증"합니다. 실제 환경은 v4.33.0-rc1 / `93594942`입니다(리드 확인).
- **Mock2_Advanced**: Section53/54의 `correctedAndProved`(28029–28052, 28689–28699)는 퇴화 모델의 존재에 근거합니다.
- **반대 방향의 과소 표기**: Spt7은 진짜 Tor 브리지를 아직 `…Pending`으로 둡니다(14620).

### 4.6 정직성 측면의 장점

- **스스로 범위를 밝힘**
  - Mock1: `doesNotProve` 경계표와 `canClaimCompleteNow = false`(2278)
  - QYM: 머리말 면책 문구(436–453)
  - Mock2_FA: `p10P11_honestDependencyAudit_endpoint` (57088)
  - Mock1_Advanced: 해석 플래그를 `false`로 기록(70934–70952)
- **명시적 의무를 분리했다가 뒤에서 해소하는 패턴**: Mock2_FA와 QYM 중반부에서 일관되게 보입니다. 이것이 "조건부 인증"이 원래 가야 할 모습입니다.
- **논문 반증·정정을 Lean 정리로 수행**(20건 이상, 대표 사례)
  - 국소화된 교집합 두께는 min이 아니라 max (Spt3 866, Spt7 2570, `Verification.lean`)
  - Prop 4.23 / Thm A.7의 간극 추론 반례 2건 (QYM 5510, 30033)
  - Def 11 π 비정합, Γ(2)가 ∞를 0으로 보내지 못함, Prop 14 수송 유일성 실패 (Mock2 9595, 21662, 22443)
  - 외삽 tube 거짓, Mahler 행렬 방향 오표기, χ₋₄ 패리티, Cardy 상수 4배 차이 (Mock1_Advanced 64710, 64952, 66797, 69699)
  - τ 표 오류 (Spt2 5163), unique lift ⇏ unit derivative (Spt6 1255)

---

## 5. "조건부 인증형 형식화" 방법론 평가

조건부 인증 자체는 타당하고 가치 있는 전략입니다. 깊은 입력을 이름 붙은 가설로 분리하고 나머지를 기계 검증하는 방식입니다. 이 저장소는 그 전략이 **잘 작동한 모습과 실패한 모습을 함께** 보여 줍니다.

| 잘 작동한 경우 (FA, QYM 중반, Mock2_Advanced) | 실패한 경우 (Spt 계열 헤드라인, Mock1, Mock1_Advanced) |
|---|---|
| 가설이 결론보다 **엄격히 약한** 별도 명제입니다(예: 트레이스 추정, 곡선 경계 Stokes). | 가설이 결론과 **같거나** `Iff.rfl`·한 단계 `le_trans` 차이입니다. |
| 가설을 뒤의 Extension에서 **실제로 증명해 해소**합니다(10개 이상). | 가설을 해소하지 않고, 상태 원장이 결과를 "UNCONDITIONAL"로 표기합니다. |
| 인스턴스가 실제 Γ(2)·η·Δ 같은 **진짜 대상**입니다. | 인스턴스가 영함수·자명 구간·`True`로 채워져 "인증서가 존재한다"는 것 외에 정보가 없습니다. |
| 미해결 입력을 docstring에 정확한 형태로 남깁니다. | 인터페이스 자체가 만족 불가능하거나(Spt7) 실제 대상을 배제합니다(Mock2 `CommonAnnulus`, Mock1_Advanced 엔트로피 입력). |

조건부 정리가 의미를 가지려면 최소한 다음 세 가지가 필요합니다.

1. **비순환성**: 가설에서 결론이 한 줄(`h x`, `h.1`, `Iff.rfl`)로 나오지 않아야 합니다.
2. **만족 가능성**: 가설을 실제 대상에 대해 채울 수 있다는 증거가 있어야 합니다. 최소한 `IsEmpty`가 아니라는 확인이 필요합니다.
3. **비자명성**: 인스턴스가 결론을 자명하게 만드는 퇴화 데이터가 아니어야 합니다.

이 세 기준으로 보면 Mock2_FunctionalAnalysis는 대체로 통과합니다. 반면 Spt 계열 헤드라인과 Mock1_Advanced는 대부분 통과하지 못합니다.

---

## 6. 공학·유지보수 측면

- **파일 구성**: 단일 파일이 최대 90,615줄입니다. Mathlib 스타일 기준인 1,500줄의 수십 배입니다. 같은 Tor/CRT/p진 로그 코어가 5개 모듈에 각각 중복되어 있습니다.
- **스캐폴딩 규모**
  - `#print axioms` 나열: Mock1_Advanced 5,985줄, Mock2·Mock2_Advanced 각 약 2,000줄, Mock1 1,155줄 등
  - 그 밖에 문자열 레지스트리, ClaimStatus 원장, 재진술 구조체 층(예: Mock1_Advanced의 CertificationReadiness → … → CompletionLedger)
- **빌드 설정**: `lakefile.lean`에 `PrimalitySheafVerification` 라이브러리 대상이 없어서 `lake build`로 빌드되지 않습니다(`lake env lean -o`로 수동 컴파일). `PrimalitySheafVerification/README.md`는 낡았습니다. `v4.30.0-rc1`과 `Verification.lean`만 설명합니다.
- **CI/자동화 흔적**
  - 워크플로 파일 **1,015개**(상류 58개)와 추가 스크립트 **1,301개**가 있습니다.
  - Lean이 아닌 추가분이 약 **172만 줄**로, Lean 코드의 약 5배입니다.
  - 워크플로 이름(`codex-fa-after3327…`, `gpt-qym-gb83…` 등)에서 AI 에이전트가 반복 수정한 흔적이 보입니다. 결과적으로 무엇이 최종 상태인지 저장소만으로는 알기 어렵습니다.
- **mathlib 포크 안에 프로젝트를 둔 구조**: 상류를 따라가기 어렵습니다. 별도 Lake 프로젝트에서 Mathlib를 의존성으로 두는 편이 낫습니다.

---

## 7. 권고사항 (우선순위 순)

1. **순환 정리를 정리하세요.** 이름 붙은 가설을 그대로 적용해서 끝나는 정리 191개를 목록화하고, 각각을 다음 중 하나로 처리하세요.
   - (a) 삭제
   - (b) "정의 재진술"로 이름 변경
   - (c) 실제로 더 약한 가설로 교체

   `AKSIsComplete`류 정리는 "인증된" 목록에서 빼야 합니다.
2. **만족 가능성 검사를 의무화하세요.** 가설로 쓰는 모든 인터페이스·인증서에 대해 "실제 대상 위의 인스턴스" 또는 최소한 비공허성 정리를 요구하세요. Spt7 인터페이스는 다음 중 하나로 고쳐야 합니다.
   - 0이 아닌 유한생성 모듈과 Noether 국소환으로 범위 제한
   - Mathlib의 depth 이론으로 교체
   - 삭제

   Mock1_Advanced의 엔트로피 입력은 상수를 α = π/√6, β = −log 2로 바로잡거나 삭제해야 합니다.
3. **reference 인스턴스는 스모크 테스트로만 쓰세요.** 이름을 `smokeTest…` 등으로 바꾸고 상태 판정 근거에서 빼세요.
4. **상태 원장을 Lean에서 기계적으로 생성하세요.** 손으로 쓴 String/Bool 원장 대신, 공리 감사(예: [`verification/AxiomAudit.lean`](verification/AxiomAudit.lean))와 가설 분류에서 자동 생성하세요. 주석 처리된 정리를 `.unconditional`로 표기하는 일을 원천 차단할 수 있습니다.
5. **구조를 정비하세요.**
   - 공통 코어(Tor·CRT·p진 로그·Γ(2))를 하나의 라이브러리로 묶으세요.
   - 거대 파일을 주제별 모듈로 쪼개세요.
   - `lean_lib PrimalitySheafVerification`을 추가하세요.
   - 독립 Lake 프로젝트로 옮기세요.
6. **CI를 정리하세요.** 일회성 워크플로 950개 이상을 보관하거나 삭제하고, 빌드와 공리 감사를 하는 워크플로 하나만 남기세요.
7. **Mathlib 기여 후보**
   - `adjoint_adjoint_eq_closure` (FA 25209/25307)
   - 콤팩트 K에 대해 I−K의 치역이 닫혀 있고 그 직교여공간이 유한차원 (FA 3241, 47786)
   - Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd
   - `natTrans_leftDerived_add` (Spt3 5917)
   - Jacobi 공식과 det–trace 항등식 (Spt7)
   - `formallyEtale_iff_squarefree_of_ne_zero` (Spt2 1825)
   - Γ(2) 생성원 (M2A 20785)과 Γ(2) 기본영역 (FA 6097)
8. **논문 개정**: §4.6의 반증·정정 목록을 원고에 반영하는 것을 권합니다. 형식화가 실제로 수학을 개선한 부분이므로 논문의 강점이 될 수 있습니다.

---

## 8. 이 평가의 신뢰도와 한계

- **리드가 직접 확인한 것**
  - Mathlib 무변조, 컴파일 결과, 공리 전수 감사(카나리아 포함)
  - Spt7 공허성(Lean 증명), Spt3 `AKSIsComplete` 원문, Mock1_Advanced 퇴화 인스턴스 원문, 환경 핀 문자열과 존재하지 않는 파일
  - Ramanujan f(q) 16계수(독립 계산과 일치), 엔트로피 상수의 발산(수치), Γ(0,4π) 값, 𝔽₅·𝔽₇ 곡선 점 개수
- **에이전트에 의존한 것**
  - 각 모듈의 헤드라인 정리 분류, 실질 수학 비율, 대부분의 행 번호 인용
  - 모든 줄 범위를 배정했지만, 기계적 상용구는 도구로 훑어 읽었습니다(accessor 연속 구간, `#print axioms`, Mock1_Advanced 49201–64159의 표본 정독 등). 범위는 각 보고서의 커버리지 로그에 있습니다.
- **수정한 에이전트 오류**: 한 에이전트는 f(q) 점근 상수를 β = −1/2로 적었습니다. 정확한 값은 β = −log 2입니다(Andrews–Dragonette). 결론, 즉 파일 상수로는 인스턴스를 만들 수 없다는 점은 변하지 않습니다.
- **점수의 성격**: 점수는 같은 루브릭에 따른 판단이며 정량 측정이 아닙니다. 실질 수학 비율도 추정치입니다.
- **평가 범위 밖**: 논문 원고(507쪽 아이디어 스케치) 자체는 이 평가에서 직접 대조하지 않았습니다. "논문 주장"은 Lean 파일의 docstring과 원장에 적힌 내용을 기준으로 삼았습니다.

---

## 부록 A. 재현 방법

```bash
# 1) 대상 체크아웃
git clone --branch formalization-final-authority-2026-08-21 https://github.com/leegahuyn/mathlib4
cd mathlib4
# 2) Mathlib 빌드 (캐시가 가능하면 `lake exe cache get`)
lake build Mathlib
# 3) 모듈 컴파일 (의존 순서: Mock2 → Mock2_Advanced → Mock2_FunctionalAnalysis → Integrated → QYM → Mock3)
#    audit/verification/build_psv.sh 참고
# 4) 공리 전수 감사 / Spt7 반증
lake env lean audit/verification/AxiomAudit.lean
lake env lean audit/verification/Spt7Vacuity.lean
```

## 부록 B. 파일 목록

- `modules/`: 모듈별·구간별 상세 감사 보고서(한국어)와 커버리지 로그
- `verification/build_status.txt`: 모듈별 컴파일 결과
- `verification/axiom_audit.log`: 공리 전수 감사 출력
- `verification/AxiomAudit.lean`: 공리 감사 Lean 파일 (카나리아 포함)
- `verification/Spt7Vacuity.lean`: Spt7 인터페이스 만족 불가능성 증명
- `verification/lean_scan.py`, `verification/scan_stats.json`: 정적 스캐너와 통계
- `verification/build_psv.sh`: 빌드 스크립트
