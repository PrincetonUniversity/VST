#!/usr/bin/env bash
grep -E -v -f - assumptions.txt <<EOF 
^Axioms:
^ClassicalDedekindReals.sig_not_dec( |[[:space:]]*$)
^ClassicalDedekindReals.sig_forall_dec( |[[:space:]]*$)
^prop_ext( |[[:space:]]*$)
^Events.inline_assembly_sem( |[[:space:]]*$)
^functional_extensionality_dep( |[[:space:]]*$)
^Events.external_functions_sem( |[[:space:]]*$)
^Eqdep.Eq_rect_eq.eq_rect_eq( |[[:space:]]*$)
^Classical_Prop.classic( |[[:space:]]*$)
^[ ]
EOF
if [ $? -ne 0 ]; then
   echo "Success! No unexpected assumptions"
else
    echo "Failure: Unexpected assumptions"
    
    exit 1
fi

