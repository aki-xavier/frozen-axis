#!/usr/bin/env bash
# 打包 lean-proof 的 Lean 源代码为 zip。
# 收录:全部 .lean 源文件、lean-toolchain、lake-manifest.json(版本锁定,保证可复现构建)。
# 排除:.lake/(olean/ir 编译缓存与 mathlib 等依赖克隆)、.git/、.DS_Store 等杂项文件。
# 用法: ./package-lean-proof.sh [输出路径.zip]   默认输出 <repo>/lean-proof.zip
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC_DIR="$SCRIPT_DIR/lean-proof"
OUTPUT="${1:-$SCRIPT_DIR/lean-proof.zip}"

if [[ ! -d "$SRC_DIR" ]]; then
  echo "error: 源码目录不存在: $SRC_DIR" >&2
  exit 1
fi

# 归一化为绝对路径,避免 cd 进源码目录后相对输出路径落空
OUTPUT="$(cd "$(dirname "$OUTPUT")" && pwd)/$(basename "$OUTPUT")"
rm -f "$OUTPUT"

cd "$SRC_DIR"
find . -type f \
  \( -name '*.lean' \
     -o -name 'lean-toolchain' \
     -o -name 'lake-manifest.json' \
     -o -name 'lakefile.toml' \) \
  -not -path './.lake/*' \
  -not -path './.git/*' \
  -not -name '.DS_Store' \
  | sed 's|^\./||' \
  | sort \
  | zip -q "$OUTPUT" -@

echo "已打包到 $OUTPUT,内容如下:"
zipinfo -1 "$OUTPUT"
