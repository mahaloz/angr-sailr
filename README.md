# angr sailr
The frozen version of [angr](https://github.com/angr/angr) that was used in the USENIX 2024 paper 
["Ahoy SAILR! There is No Need to DREAM of C: A Compiler-Aware Structuring Algorithm for Binary Decompilation"](https://www.zionbasque.com/files/publications/sailr_usenix24.pdf).

## Installation & Usage
The SAILR algorithm has been fully integrated into the latest angr, but if you want to use the exact version that was used in the paper, 
you can use our Docker container to run this version. This version aligns with commit [a8bab649cfc18912d5bb3ce70ef57a4ae4039f53](https://github.com/angr/angr/commit/a8bab649cfc18912d5bb3ce70ef57a4ae4039f53)
of the angr repository. It contains our submission versions of the following structuring algorithms:
- SAILR
- DREAM
- Phoenix
- Phoenix Improved
- Combing 

Please follow the instructions [here](https://github.com/mahaloz/sailr-eval/blob/ae5069ab171c35eb3d435b9b66e182354d2a427d/misc/reproducing_sailr_paper/README.md?plain=1#L16), 
for how to build/use the Docker container. Building that image will clone this repository and the angr-dev repository at the correct commit.