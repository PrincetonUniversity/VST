# Continuous Integration Provider Travis

Travis CI is controlled by the files `.travis.yml`.
See [Travis Doc](https://docs.travis-ci.com) for reference.

The main actions of the YAML script are:

- Add the coq/core-dev, coq/released and the local opam-prerelease repos to opam.
- Install opam packages coq-compcert and coq-compcert-32.
- For BITSIZE=32 run the shell script .travis-script with these options:
  - `./.travis-script floyd`
  - `./.travis-script progs`
  - `./.travis-script sha-hmac`
  - `./.travis-script mailbox`
  - `./.travis-script VSUpile`
- For BITSIZE=64 run the shell script .travis-script with these options:
  - `./.travis-script floyd`
  - `./.travis-script progs64`

Travis CI uses a **build cache** to speed up CI.
The build cache is kept per branch/PR.
The build cache can lead to **issues** if substantial changes to the directory structure are made.
In this case the travis build cache should be reset.
If you need to reset the cache, navigate to (https://travis-ci.com/github/PrincetonUniversity/VST) and sign in (typically using your GitHub account).
At the top right of the list there is "More options" menu - select "Caches".

# Continuous Integration Provider GitHub actions

GitHub Actions CI is controlled by the file `.github/workflows/coq-action.yml`.
See [GitHub Actions Doc](https://docs.github.com/en/free-pro-team@latest/actions/reference/workflow-syntax-for-github-actions) for reference.

The GitHub action is split into a `build` and one or multiple `test` jobs.
The `build` job uploads the dependencies installed via opam (the `user-contrib` folder) and the
VST working folder as compressed tar file.
The one or more `test` jobs download this `.tgz` file tp continue at the point where the `build`job left.
The main advantage of this setup is that several test jobs can be run in parallel.

The main actions of the `build` part are:

- check out the branch from GIT
- download a Coq docker image via (https://github.com/coq-community/docker-coq-action/tree/v1.0.0)
- the Coq docker images are provided by (https://github.com/coq-community/docker-coq/wiki)
- add the local opam-prerelease repo (coq/released is already available in the docker image)
- install the dependency `coq-compcert`
- run `make vst BITSIZE=32/64`
- copy `lib/coq/user-contrib` to the working folder
- tar gz the working folder and upload it as build artifact

The main actions of the `test` part(s) are:

- download and extract the working folder created by the `build` stage
- download a Coq docker image
- copy the backup of `lib/coq/user-contrib` to the destination folder
- run `make test BITSIZE=32/64` where `test` is a make target

The GitHub actions are based on a parameter matrix.
The above set of actions is performed for various combination of these parameters:
- coq_version (8.13, 8.14. 8.15)
- make_target (`vst` for `build` or `test`for `test`)
- bit_size (32 or 64)
Some combinations are excluded for efficiency reasons.
