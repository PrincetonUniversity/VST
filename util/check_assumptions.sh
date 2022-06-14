#!/usr/bin/env bash
grep -v -f - assumptions.txt <<EOF 
^Axioms:
^ClassicalDedekindReals.sig_not_dec[^[:alnum:]_]
^ClassicalDedekindReals.sig_forall_dec[^[:alnum:]_]
^prop_ext[^[:alnum:]_]
^Events.inline_assembly_sem[^[:alnum:]_]
^functional_extensionality_dep[^[:alnum:]_]
^Events.external_functions_sem[^[:alnum:]_]
^Eqdep.Eq_rect_eq.eq_rect_eq[^[:alnum:]_]
^Classical_Prop.classic[^[:alnum:]_]
^[ ]
EOF
if [ $? -ne 0 ]; then
   echo "Success! No unexpected assumptions"
else
    echo "Failure: Unexpected assumptions"
    exit 1
fi

