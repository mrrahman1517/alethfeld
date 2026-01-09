#!/bin/bash
# Installation script for Clojure and LaTeX tools required for Alethfeld

set -e

echo "=========================================="
echo "Alethfeld Tools Installation Script"
echo "=========================================="
echo ""

# Check if running as root
if [ "$EUID" -eq 0 ]; then 
   echo "Please do not run this script as root. It will use sudo when needed."
   exit 1
fi

# Update package list
echo "Step 1: Updating package list..."
sudo apt update

# Install Clojure CLI Tools
echo ""
echo "Step 2: Installing Clojure CLI Tools..."
# Check if clj (CLI tools) is available
if command -v clj &> /dev/null; then
    echo "Clojure CLI Tools (clj) found: $(clj --version 2>/dev/null | head -1 || echo 'version check failed')"
    CLOJURE_CMD="clj"
elif command -v clojure &> /dev/null; then
    # Test if it's the CLI tools version (supports -T flag)
    if clojure -T:build help &>/dev/null 2>&1 || clojure -Spath &>/dev/null 2>&1; then
        echo "Clojure CLI Tools found: $(clojure --version 2>/dev/null | head -1 || echo 'version check failed')"
        CLOJURE_CMD="clojure"
    else
        echo "WARNING: Found 'clojure' command but it appears to be the old REPL version, not CLI tools."
        echo ""
        echo "The Alethfeld CLI requires Clojure CLI Tools (clj), not the old REPL."
        echo ""
        echo "Installing Clojure CLI Tools using official installer..."
        INSTALLER="/tmp/clojure-install.sh"
        echo "Downloading installer..."
        if curl -L https://download.clojure.org/install/linux-install-1.11.1.1347.sh -o "$INSTALLER" 2>/dev/null; then
            chmod +x "$INSTALLER"
            echo "Running installer (requires sudo)..."
            sudo "$INSTALLER"
            rm -f "$INSTALLER"
        else
            echo "ERROR: Failed to download installer."
            echo ""
            echo "Please install Clojure CLI Tools manually:"
            echo "  1. Visit: https://clojure.org/guides/install_clojure"
            echo "  2. Or use SDKMAN:"
            echo "     curl -s \"https://get.sdkman.io\" | bash"
            echo "     source \"\$HOME/.sdkman/bin/sdkman-init.sh\""
            echo "     sdk install clojure"
            echo ""
            echo "After installation, run this script again or build manually:"
            echo "  cd cli && clojure -T:build uber"
            exit 1
        fi
        
        # Reload PATH
        export PATH="$HOME/.clojure/bin:$PATH"
        if command -v clj &> /dev/null; then
            CLOJURE_CMD="clj"
            echo "✓ Clojure CLI Tools installed successfully."
        else
            echo "Installation completed. Please restart your shell or run:"
            echo "  export PATH=\"\$HOME/.clojure/bin:\$PATH\""
            CLOJURE_CMD="clj"  # Assume it will work after PATH update
        fi
    fi
else
    echo "Clojure CLI Tools not found. Installing..."
    INSTALLER="/tmp/clojure-install.sh"
    echo "Downloading installer..."
    if curl -L https://download.clojure.org/install/linux-install-1.11.1.1347.sh -o "$INSTALLER" 2>/dev/null; then
        chmod +x "$INSTALLER"
        echo "Running installer (requires sudo)..."
        sudo "$INSTALLER"
        rm -f "$INSTALLER"
    else
        echo "ERROR: Failed to download installer."
        echo ""
        echo "Please install Clojure CLI Tools manually:"
        echo "  1. Visit: https://clojure.org/guides/install_clojure"
        echo "  2. Or use SDKMAN:"
        echo "     curl -s \"https://get.sdkman.io\" | bash"
        echo "     source \"\$HOME/.sdkman/bin/sdkman-init.sh\""
        echo "     sdk install clojure"
        exit 1
    fi
    
    # Reload PATH
    export PATH="$HOME/.clojure/bin:$PATH"
    CLOJURE_CMD="clj"
    echo "✓ Clojure CLI Tools installed successfully."
fi

# Install LaTeX
echo ""
echo "Step 3: Installing LaTeX (pdflatex)..."
if command -v pdflatex &> /dev/null; then
    echo "pdflatex is already installed: $(pdflatex --version | head -1)"
else
    echo "Installing texlive-latex-base and texlive-latex-extra..."
    sudo apt install -y texlive-latex-base texlive-latex-extra
    echo "LaTeX installed successfully: $(pdflatex --version | head -1)"
fi

# Build Alethfeld CLI
echo ""
echo "Step 4: Building Alethfeld CLI..."
cd ../../cli
if [ -f "target/alethfeld.jar" ]; then
    echo "Alethfeld CLI already built."
else
    echo "Building alethfeld.jar using $CLOJURE_CMD..."
    # Ensure PATH includes Clojure CLI tools
    export PATH="$HOME/.clojure/bin:$PATH"
    
    # Try building with the detected command
    if $CLOJURE_CMD -T:build uber 2>/dev/null; then
        echo "✓ Built successfully using $CLOJURE_CMD -T:build uber"
    else
        echo "WARNING: Failed to build alethfeld.jar with $CLOJURE_CMD -T:build uber"
        echo ""
        echo "This might be because:"
        echo "  1. Clojure CLI Tools are not in PATH (try: export PATH=\"\$HOME/.clojure/bin:\$PATH\")"
        echo "  2. The build tools need to be downloaded first"
        echo ""
        echo "You can try manually:"
        echo "  cd cli"
        echo "  export PATH=\"\$HOME/.clojure/bin:\$PATH\""
        echo "  clj -T:build uber"
        echo ""
        echo "For now, you can still use the LaTeX file directly."
    fi
    
    if [ -f "target/alethfeld.jar" ]; then
        echo "✓ Alethfeld CLI built successfully at target/alethfeld.jar"
    fi
fi

echo ""
echo "=========================================="
echo "Installation Complete!"
echo "=========================================="
echo ""
echo "Installed tools:"
if [ -n "$CLOJURE_CMD" ]; then
    echo "  - Clojure CLI: $($CLOJURE_CMD --version 2>/dev/null | head -1 || echo 'Installed but version check failed')"
else
    echo "  - Clojure CLI: Not found (installation may have failed)"
fi
echo "  - pdflatex: $(pdflatex --version 2>/dev/null | head -1 || echo 'Not found')"
echo ""
echo "Next steps:"
echo "  1. Test LaTeX compilation:"
echo "     cd examples/sum-degrees-even"
echo "     pdflatex sum-degrees-even.tex"
echo ""
echo "  2. Test Alethfeld CLI:"
echo "     cd cli"
echo "     ./scripts/alethfeld stats ../examples/sum-degrees-even/sum-degrees-even.edn"
echo ""
