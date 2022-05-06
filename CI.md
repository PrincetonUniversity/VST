# Continuous Integration Provider: GitHub actions

[in early 2022 we discontinued the use of Travis-CI]

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
