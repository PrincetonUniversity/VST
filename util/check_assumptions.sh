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
^Clight_core.inline_external_call_mem_events( |[[:space:]]*$)
^lib.Axioms.proof_irr( |[[:space:]]*$)
^[ ]
EOF
if [ $? -ne 0 ]; then
   echo "Success! No unexpected assumptions"
else
    echo "Failure: Unexpected assumptions.  The axiom(s) listed on the lines above are not in the standard Trusted Base of VST.  Perhaps you have an Admitted lemma?"
    
    exit 1
fi

