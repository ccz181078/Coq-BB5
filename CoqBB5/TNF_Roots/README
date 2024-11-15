# TNF Roots

In order to parallelise the proof, the [TNF tree](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF_Enumeration) has been manually split into several subtrees, each handled by one file.

The original root of the tree is the completely undefined Turing machines, it has 8 children:

- `BB52Theorem_root1.v`: explores `0RA---_------_------_------_------`
- `BB52Theorem_root2.v`: explores `1RA---_------_------_------_------`
- `BB52Theorem_root3.v`: explores `0RB---_------_------_------_------`
- `BB52Theorem_root4.v`: `1RB---_------_------_------_------`, this node is further expanded to its 12 children.
- The four other roots use direction `L` and don't have to be searched by symmetrising their computation to using `R` instead.

`root_4` is further expanded, it has 12 children:

- `BB52Theorem_root4_trivial.v`: explores 4 "trivial" children (i.e. these are leaves of the tree as they are easily proven non-halting as they drift to the right forever):
    - `1RB---_0RA---_------_------_------`
    - `1RB---_1RA---_------_------_------`
    - `1RB---_0RB---_------_------_------`
    - `1RB---_1RB---_------_------_------`

- 8 "nontrivial" children (i.e. these are not leaves):
    - `BB52Theorem_root4_nontrivial_1.v`: explores `1RB---_0LA---_------_------_------`
    - `BB52Theorem_root4_nontrivial_2.v`: explores `1RB---_1LA---_------_------_------`
    - `BB52Theorem_root4_nontrivial_3.v`: explores `1RB---_0LB---_------_------_------`
    - `BB52Theorem_root4_nontrivial_4.v`: explores `1RB---_1LB---_------_------_------`
    - `BB52Theorem_root4_nontrivial_5.v`: explores `1RB---_0LC---_------_------_------`
    - `BB52Theorem_root4_nontrivial_6.v`: explores `1RB---_1LC---_------_------_------`
    - `BB52Theorem_root4_nontrivial_7.v`: explores `1RB---_0RC---_------_------_------`
    - `BB52Theorem_root4_nontrivial_8.v`: explores `1RB---_1RC---_------_------_------`

Here are indicative compile times for each of these roots (using native_compute on an Apple M3 Max, 32 Gb):

| Root                | time      |
|---------------------|-----------|
| root_1              | 2.5s      |
| root_2              | 2.5s      |
| root_3              | **29.8m** |
| root_4_trivial      | 2.97s     |
| root_4_nontrivial_1 | 1.6m      |
| root_4_nontrivial_2 | 4m        |
| root_4_nontrivial_3 | 58s       |
| root_4_nontrivial_4 | 2.4m      |
| root_4_nontrivial_5 | 11.5m     |
| root_4_nontrivial_6 | **28.5m** |
| root_4_nontrivial_7 | 14.8m     |
| root_4_nontrivial_8 | **21m**   |

This table indicates that to get a significant parallel speed up one should further expand `root_3`, `root_4_nontrivial_6` and `root_4_nontrivial_8`. Note as well that `root_3` corresponds to `0RB---_------_------_------_------` and could be completely skipped as it is known that exploring this subtree(i.e. where a 0 is first written) is not needed to conclude on the value of `S(n)` or `\Sigma(n)` [(source 1)](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF-1RB) [(source 2)](https://discord.com/channels/960643023006490684/1239205785913790465/1242407785736441948) [(source 3)](https://github.com/meithecatte/busycoq/blob/master/verify/Enumerate.v#L118-L121).