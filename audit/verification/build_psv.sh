#!/bin/bash
# Resume Mathlib build, then compile the PSV modules in dependency order.
export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/bin:$PATH
S=/tmp/claude-0/-home-user-FORMALIZATION-OF-MY-10-PAPERS/4188b314-1f9c-511e-9652-2dbe2485c5da/scratchpad
L=$S/buildlogs
cd /home/user/leegahuyn/mathlib4
echo "mathlib start $(date -u +%FT%TZ)" >> $L/STATUS
lake build Mathlib > $L/mathlib.log 2>&1
echo "mathlib exit=$? $(date -u +%FT%TZ)" >> $L/STATUS
O=.lake/build/lib/lean/PrimalitySheafVerification
mkdir -p $O
compile() {
  local m=$1
  grep -q "^$m exit=" $L/STATUS 2>/dev/null && return 0
  local t0=$(date +%s)
  lake env lean -DmaxErrors=2000 -o $O/$m.olean -i $O/$m.ilean PrimalitySheafVerification/$m.lean > $L/$m.log 2>&1
  local rc=$?
  local e=$(grep -cE "^PrimalitySheafVerification/$m.lean:[0-9]+:[0-9]+: error" $L/$m.log)
  local w=$(grep -cE "^PrimalitySheafVerification/$m.lean:[0-9]+:[0-9]+: warning" $L/$m.log)
  local s=$(grep -c "declaration uses 'sorry'" $L/$m.log)
  local rss=NA
  echo "$m exit=$rc errors=$e warnings=$w sorry_warnings=$s secs=$(( $(date +%s)-t0 )) maxrss_kb=$rss" >> $L/STATUS
}
export -f compile; export O L
# independent modules, two at a time
printf "%s\n" Spt3 Spt2 Spt4 Spt5 Spt6 Spt7 Mock1 Mock2 Spt1 | xargs -P2 -I{} bash -c 'compile {}'
compile Mock2_Advanced
compile Mock2_FunctionalAnalysis
compile Mock2_FunctionalAnalysis_Integrated
compile QYM
compile Mock3
compile Mock1_Advanced
compile BuildAll
echo "ALL DONE $(date -u +%FT%TZ)" >> $L/STATUS
