Reification using mirror-shard

This folder uses its own build path because it depends on
coq-ext-lib and a branch of mirror-shard.
These can be downloaded at

https://github.com/dist0rtedwave/mirror-shard
https://github.com/coq-ext-lib/coq-ext-lib

mirror-shard should be in the same folder as vst and coq-ext-lib
should be inside of the mirror-shard folder. 

top
|-mirror-shard
    |-coq-ext-lib
    |-src
    |-...
|-vst
    |-reify
    |-floyd
    |-...

mirror-shard can be built by first building coq-ext-lib and
then building mirror-shard

vst can be built by following the directions in
vst/BUILD_ORGANIZATION

once both have built successfully 
(it is ok if some mirror-shard examples fail to build, and you will only
 need list_dt and the clight (.v) file for the example you wish to reify
 in the vst progs directory)
run make in the reify directory.

Warnings about loadpath are expected, and appear because we don't build
dependencies outside of this folder.
