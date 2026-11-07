# 按经典 LaTeX 论文方式重组目录

## Context

当前论文已有独立的 `sections/` 和 `figures/`，但论文入口、样式、参考文献、构建工具、发布文件和大量本地编译产物都堆在仓库根目录。用户已确认采用独立的 `paper/` 论文工程，与 `experiments/`、`lean-proof/` 分开；仅重组目录及修复路径，不改动论文内容、章节顺序、JMLR 样式或 Lean 实现。

## 目标结构

```text
paper/
├── main.tex
├── paper-slim.tex
├── paper.tex                 # flatten 生成的受控文件
├── reference.bib
├── sections/*.tex
├── figures/probe.pdf
├── styles/jmlr2e.sty
├── appendix/{main.tex,body.tex}
└── latexmkrc
scripts/{build.sh,flatten.py}
dist/                          # 现有 PDF 和 DOCX 发布/导出文件
build/                         # 忽略的新编译输出及旧产物归档
experiments/                   # 保持独立
lean-proof/                    # 保持独立
```

`dist/` 收纳现有 `paper.pdf`、`paper-slim.pdf`、`online-appendix.pdf`、`main.pdf` 和 `paper.docx`。`main.pdf`、`paper.docx` 只迁移位置，不新增生成流程。

## 实施步骤

1. **迁移源文件，保留 Git 历史**
   - 使用 `git mv` 将根目录主论文、精简稿、生成稿、参考文献、章节和图片移入 `paper/`。
   - 将未改动的 JMLR 样式移到 `paper/styles/jmlr2e.sty`，在线附录移到 `paper/appendix/`。
   - 将 `build.sh`、`flatten.py` 移到 `scripts/`，`latexmkrc` 移到 `paper/latexmkrc`。
   - 将现有发布/导出文件移入 `dist/`；`experiments/`、`lean-proof/` 和根目录许可证保持原位。
   - 移动前检查 Git 状态，避免覆盖已有本地修改。

2. **修复 LaTeX 路径**
   - 从 `paper/` 目录编译，保持 `main.tex` 的 `sections/...`、`reference` 和章节中的 `figures/probe.pdf` 路径不变。
   - 在 `paper/main.tex` 与 `paper/paper-slim.tex` 中将样式引用改为 `styles/jmlr2e`。
   - 在 `paper/appendix/main.tex` 中将正文引用改为 `body`，更新其中失效的构建命令注释。
   - 不手工修改生成的 `paper/paper.tex`，由 flatten 工具重新生成。

3. **调整构建与生成工具**
   - `scripts/build.sh` 区分仓库根目录、论文目录和脚本目录，以 `paper/` 为编译工作目录；入口映射为 `main.tex`、`paper.tex`、`paper-slim.tex`、`appendix/main.tex`。
   - 中间产物统一输出到根目录 `build/{main,paper,slim,appendix}/`，使用绝对路径避免工作目录切换造成错放。
   - `latexmkrc` 随论文放在 `paper/`，由其自动发现；保留 pdflatex、BibTeX、错误检测、固定时间戳和构建失败不覆盖发布文件的现有机制。
   - 发布 PDF 写入 `dist/`，递归构建附录时仍使用同一脚本；保持 `main` 目标只生成 `build/main/main.pdf`。
   - `scripts/flatten.py` 明确入口和输出均在 `paper/`，生成注释与内联来源路径使用论文目录相对路径。
   - `experiments/probe.py` 的图片输出改为 `paper/figures/probe.pdf`；实验数据路径不变。

4. **同步仓库说明与忽略规则**
   - 更新 `README.md` 的目录表、PDF 链接、`./scripts/build.sh ...`、`python3 scripts/flatten.py`、图片输出和许可证路径说明；不新增额外文档。
   - 更新 `CITATION.cff` 中 `paper.pdf` 位于根目录的说明，指向 `dist/paper.pdf`。
   - `.gitignore` 忽略统一 `/build/`，保留 LaTeX 中间文件和 Python 缓存规则；不忽略 `dist/`。
   - 本地投稿材料 `cover-letter.tex`、`journal-selection.md`、`review.md`、`revision-plan.md`、`response-letter.md` 不移动、不改写，`.git/info/exclude` 不需要变更。

5. **保留旧编译产物**
   - 不运行 `rm`、`git clean` 或清空命令。将旧 `build-*` 目录及根目录 `.aux/.log/.out/.bbl/.blg/.fdb_latexmk/.fls` 移入 `build/legacy/`（被 Git 忽略），使根目录整洁且不丢失本地产物。
   - `__pycache__`、`.DS_Store` 和 Lean 缓存不属于本次 LaTeX 目录重组，保持不动。

## 验证

1. 执行 `python3 scripts/flatten.py`，确认生成 `paper/paper.tex`，其样式、图片和参考文献路径正确。
2. 执行 `./scripts/build.sh main`、`./scripts/build.sh slim`、`./scripts/build.sh release`，覆盖模块化论文、精简稿、单文件发布稿及独立附录；检查错误、未定义引用、缺失图片及 BibTeX 警告。
3. 在全新的 `build/main/` 上执行 `USE_LATEXMK=0 ./scripts/build.sh main`，验证无 latexmk 时 BibTeX 仍从 `paper/` 找到 `reference.bib`。
4. 用 `cmp` 核对 `build/paper/paper.pdf` 与 `dist/paper.pdf`、精简稿及附录发布文件；内容未变时发布 PDF 应仅表现为 Git 重命名。
5. 运行 `git diff --check`、`git status --short` 和 `git diff --stat`，检查意外正文差异、遗漏的旧路径及应被忽略的构建产物；不创建 Git 提交。

## 关键文件

- `paper/main.tex`、`paper/paper-slim.tex`、`paper/appendix/main.tex`
- `scripts/build.sh`、`scripts/flatten.py`、`paper/latexmkrc`
- `experiments/probe.py`
- `README.md`、`CITATION.cff`、`.gitignore`
