#!/bin/sh
# Switch the long native computations between Admitted (fast) and Qed (full check).
#   ./toggle_qed.sh qed     replace each "(* Time Qed. *) Admitted." by "Time Qed."
#   ./toggle_qed.sh admit   put the Admitted back
# Only lines marked "(* toggle *)" are switched back, so other Qed are never touched.
set -e
cd "$(dirname "$0")"
case "$1" in
  qed)
    perl -0pi -e 's/\(\*[ \t]*\n((?:(?![^\n]*(?:\(\*|\*\)))[^\n]*\n)*?)Time Qed\.[ \t]*\n\*\)[ \t]*\nAdmitted\.[ \t]*/$1Time Qed. (* toggle *)/g' *.v ;;
  admit)
    perl -0pi -e 's/Time Qed\. \(\* toggle \*\)/(*\nTime Qed.\n*)\nAdmitted./g' *.v ;;
  *) echo "usage: $0 qed|admit"; exit 1 ;;
esac
echo "Admitted: $(cat *.v | grep -c '^Admitted\.') ; switched to Qed: $(cat *.v | grep -c 'toggle')"
