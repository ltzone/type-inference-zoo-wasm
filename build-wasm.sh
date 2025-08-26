#!/bin/bash

# Build script for compiling Haskell to WASM
# This script uses GHC-WASM to compile the recursive backend to WebAssembly

set -e

echo "🚀 Building WASM from Haskell..."

echo "📦 Entering nix shell with GHC-WASM..."
echo "   Note: If you get an error about experimental features, you can add:"
echo "   --extra-experimental-features nix-command --extra-experimental-features flakes"
echo ""

# Use nix shell to get the GHC-WASM environment
if ! nix shell 'gitlab:haskell-wasm/ghc-wasm-meta?host=gitlab.haskell.org' --command bash -c "
    echo '🔧 Updating cabal packages...'
    wasm32-wasi-cabal update
    
    echo '🔨 Building WASM binary (type-inference-zoo-wasm)...'
    if wasm32-wasi-cabal build; then
        echo '✅ WASM build successful!'
        exit 0
    else
        echo '❌ WASM build failed!'
        echo '   Check the error messages above for dependency issues.'
        exit 1
    fi
"; then
    echo "❌ Error: Failed to build WASM using nix shell"
    echo ""
    echo "💡 Troubleshooting tips:"
    echo "   1. Make sure you have Nix installed"
    echo "   2. Try adding experimental features:"
    echo "      nix --extra-experimental-features nix-command --extra-experimental-features flakes shell 'gitlab:haskell-wasm/ghc-wasm-meta?host=gitlab.haskell.org'"
    echo "   3. Or add to ~/.config/nix/nix.conf:"
    echo "      experimental-features = nix-command flakes"
    exit 1
fi

TARGET="type-inference-zoo-exe"
WASM_NAME="type-inference-zoo-exe.wasm"

echo "📁 Creating output directory..."
mkdir -p ../type-inference-zoo-frontend/public/wasm

echo "📋 Finding and copying WASM file..."
# Find the built WASM file and copy it to the frontend public directory
WASM_FILE=$(find ./dist-newstyle -name "$WASM_NAME" -type f | head -n 1)

if [ -z "$WASM_FILE" ]; then
    echo "❌ Error: Could not find built WASM file: $WASM_NAME"
    echo "   Searched in: ./dist-newstyle"
    exit 1
fi

echo "📋 Found WASM file: $WASM_FILE"
cp "$WASM_FILE" ../type-inference-zoo-frontend/public/wasm/bin.wasm

echo "✅ WASM build complete!"
echo "   Target: $TARGET"
echo "   Output: ../type-inference-zoo-frontend/public/wasm/bin.wasm"
echo "   Size: $(du -h ../type-inference-zoo-frontend/public/wasm/bin.wasm | cut -f1)"

echo ""
echo "🎯 Next steps:"
echo "   1. Run 'npm run dev' in the frontend directory"
echo "   2. The app will now load WASM from /wasm/bin.wasm"
echo "   3. Check browser console for WASM loading status"
