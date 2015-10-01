#!/usr/bin/env python

from subprocess import check_output
from datetime import date
import textwrap

def generate_version_file():
    git_rev = check_output(["git", "log", "-n", "1", "--pretty=format:\"%H\""]).strip().replace("\"", "")
    version_file = open("VERSION", "r")
    version = version_file.read().strip()
    version_file.close()
    today = date.today().strftime("%Y-%m-%d").strip()
    coq_version_file = open("version.v", "w")
    coq_version_file.write(textwrap.dedent("""\
        Require Import Coq.Strings.String.
        Open Scope string.
        Definition git_rev := "{0}".
        Definition release := "{1}".
        Definition date    := "{2}".
        """).format(git_rev, version, today))
    coq_version_file.close()

if __name__ == "__main__":
    generate_version_file()
