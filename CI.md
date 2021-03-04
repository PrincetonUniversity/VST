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

GitHub Actions uses the local opam files `coq-vst.opam` and `coq-vst-32.opm` to define dependencies (especially the CompCert version used), the build precedure and the make test targets. Only the version of Coq is controlled directly in the YAML file.

The main actions of the YAML script are:

- Check out the branch from CI.
- Download a Coq docker image via (https://github.com/coq-community/docker-coq-action/tree/v1.0.0).
- The Coq docker images are provided by (https://github.com/coq-community/docker-coq/wiki).
- Add the local opam-prerelease repo (coq/released is already available in the docker image).
- Install the dependencies of the local opam package `coq-vst.opam` or `coq-vst-32.opm`.
- Install the local opam package `coq-vst.opam` or `coq-vst-32.opam` with running tests.

The GitHub actions are based on a parameter matrix.
The above set of actions is performed for each combination of these parameters:
- coq_version (8.12, 8.13)
- opam_name (coq-vst, coq-vst-32)

The first parameter is the coq version part of a Coq docker image, see (https://github.com/coq-community/docker-coq/wiki) for available options.
The second parameter is the name of a local opam package file (without .opam).
It would be possible to add an additional parameter, e.g. a CompCert version or CompCert open source vs. full.
It is also possible to restrict the matrix with an `exclude:` statement, see [Exclude](https://docs.github.com/en/free-pro-team@latest/actions/reference/workflow-syntax-for-github-actions#example-excluding-configurations-from-a-matrix)

# Pros and Cons

- The build speed of Travis is slightly faster - usually Travis finishes together with the first matrix jobs from GitHub actions.
- GitHub actions does not run on branches other than the master branch and PR branches - not sure how to fix this.
- GitHub actions also checks the local opam files, so that these can serve as a template for publishing opam packages.
  Of course one could have the same functionality in Travis.
- The matrix approach of GitHub and the parallel build stages of Travis seem to be about equivalent in functionality.
- The build cache of Travis gives a larger speed advantage than Docker used in GitHub actions. In a test run (commit 9291cd3) Travis finished in 29 minutes, while GitHub actions required 55 minutes - almost twice as long.

In summary I would say that both systems are comparable in capabilities. One can probably drop one of them.
