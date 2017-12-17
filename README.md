# [LAMEVMX: LAME Ain't an MP3 Encoder with VMX](http://www.floodgap.com/software/lamevmx/)

A PowerPC-optimized build of LAME 3.100 with [tmkk's patches for AltiVec](http://tmkk.undo.jp/lame/index_e.html), enhanced with additional G5 optimizations and build-system fixes. Intended for lovely Power Macs and not icky Intel Macs, which are better served by the mainline build. Maintained by Cameron Kaiser (classilla@floodgap.com).

How to build (GNU `make` from MacPorts strongly recommended):

* Have a 10.4 system with Xcode 2.5. (It may or may not work on 10.5 with Xcode 3. It probably doesn't work on 10.6. It will *not* work on 10.7+.)
* Clone it.
* `./configure`
* `make` or `gmake`

You will have a three-headed multi-architecture binary in `frontend/lame` with versions for G3, G4 and G5 processors. The same binary runs on all systems. Do `gmake test` for a quick test of functionality.

On my Quad G5 (2.5GHz), LAMEVMX achieves approximately 25x playback speed at peak.
