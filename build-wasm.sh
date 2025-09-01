#!/bin/bash

# Build script for compiling Haskell to WASM using the ghc-wasm-meta bootstrap script.
# This ensures a stable GHC 9.6 toolchain is used.

set -e

# --- Configuration ---
# Installation directory for the Wasm toolchain
GHC_WASM_DIR="${HOME}/.ghc-wasm"
# The specific GHC version flavour to install
FLAVOUR="9.10"

# --- 1. Install Toolchain (if not already installed) ---
if [ ! -f "${GHC_WASM_DIR}/env" ]; then
  echo "🔧 GHC-WASM toolchain not found. Installing flavour '${FLAVOUR}'..."
  echo "   This will only happen once."
  
  # Set the FLAVOUR and run the bootstrap script
  FLAVOUR="${FLAVOUR}" bash -c "$(curl -sS https://gitlab.haskell.org/haskell-wasm/ghc-wasm-meta/-/raw/master/bootstrap.sh)"
else
  echo "✅ GHC-WASM toolchain already installed."
fi

# --- 2. Activate Environment ---
echo "📦 Activating GHC-WASM environment..."
source "${GHC_WASM_DIR}/env"

# --- 3. Build the Project ---
echo "🚀 Building WASM from Haskell..."

echo "🔧 Updating cabal packages..."
wasm32-wasi-cabal update

echo "🔨 Building WASM binary..."
if ! wasm32-wasi-cabal build; then
    echo "❌ WASM build failed!"
    exit 1
fi

# --- 4. Copy the Output ---
WASM_NAME="type-inference-zoo-exe.wasm"

echo "📁 Creating output directory..."
mkdir -p ../type-inference-zoo-frontend/public/wasm

echo "📋 Finding and copying WASM file..."
WASM_FILE=$(find ./dist-newstyle -name "$WASM_NAME" -type f | head -n 1)

if [ -z "$WASM_FILE" ]; then
    echo "❌ Error: Could not find built WASM file: $WASM_NAME"
    exit 1
fi

echo "📋 Found WASM file: $WASM_FILE"
cp "$WASM_FILE" ../type-inference-zoo-frontend/public/wasm/bin.wasm

echo "✅ WASM build complete!"
echo "   Output: ../type-inference-zoo-frontend/public/wasm/bin.wasm"