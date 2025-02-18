# TNF Roots

In order to parallelise the proof, the [TNF tree](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF_Enumeration) has been manually split into several subtrees, each handled by one file.

The original root of the tree is the completely undefined Turing machines, it has 8 children:

- `TNF_Root_1.v`: explores `0RA---_------_------_------_------`
- `TNF_Root_2.v`: explores `1RA---_------_------_------_------`
- `TNF_Root_3.v`: explores `0RB---_------_------_------_------`
- `TNF_Root_4.v`: `1RB---_------_------_------_------`, this node is further expanded to its 12 children.
- The four other roots use direction `L` and don't have to be searched by symmetrising their computation to using `R` instead.

`root_4` is further expanded, it has 12 children, each in subfolder `TNF_Root_4/`. Files marked with `_leaf`, such as `TNF_Root_4/TNF_Root_4_3_leaf.v` correspond to nonhalting children of `root_4` who consequently do not yield any additional subtree but are leaves of the overall TNF tree.

Here are indicative compile times for each of these roots (using native_compute on an Apple M3 Max, 32 Gb):

| Root                | time      |
|---------------------|-----------|
| root_1              | 2.5s      |
| root_2              | 2.5s      |
| root_3              | **29.8m** |
| root_4_leaves       | 2.97s     |
| root_4_1            | 1.6m      |
| root_4_2            | 4m        |
| root_4_5            | 58s       |
| root_4_6            | 2.4m      |
| root_4_9            | 11.5m     |
| root_4_10           | **28.5m** |
| root_4_11           | 14.8m     |
| root_4_12           | **21m**   |

This table indicates that to get a significant parallel speed up one should further expand `root_3`, `root_4_10` and `root_4_12`. Note as well that `root_3` corresponds to `0RB---_------_------_------_------` and could be completely skipped as it is known that exploring this subtree (i.e. where a 0 is first written) is not needed to conclude on the value of `S(n)` or `\Sigma(n)` [(source 1)](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF-1RB) [(source 2)](https://discord.com/channels/960643023006490684/1239205785913790465/1242407785736441948) [(source 3)](https://github.com/meithecatte/busycoq/blob/master/verify/Enumerate.v#L118-L121).