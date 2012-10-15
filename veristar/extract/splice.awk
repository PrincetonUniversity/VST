
BEGIN {X=0}
/end/ { X=0 }
{if (!X) { print $0 }}
/module DebuggingHooks/ { print " struct"; X=1 }
{if (X) { while (getline line <"debugging.ml") {print line} }}
END {}