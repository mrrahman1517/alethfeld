# Installation Guide

This guide explains how to install the required tools to work with Alethfeld proofs.

## Required Tools

1. **Clojure** - For running Alethfeld CLI tools
2. **LaTeX** (pdflatex) - For compiling LaTeX documents to PDF

## Installing Clojure CLI Tools

**Important:** Alethfeld requires **Clojure CLI Tools** (the `clj` command), not the old REPL-based `clojure` command. The system package `clojure` is the old version and won't work.

### Option 1: Official Installer (Recommended)

```bash
# Download and run the official installer
curl -O https://download.clojure.org/install/linux-install-1.11.1.1347.sh
chmod +x linux-install-1.11.1.1347.sh
sudo ./linux-install-1.11.1.1347.sh

# Add to PATH (add to ~/.bashrc or ~/.zshrc for persistence)
export PATH="$HOME/.clojure/bin:$PATH"
```

### Option 2: Using SDKMAN

```bash
# Install SDKMAN if not already installed
curl -s "https://get.sdkman.io" | bash
source "$HOME/.sdkman/bin/sdkman-init.sh"

# Install Clojure CLI Tools
sdk install clojure
```

### Option 3: Package Manager (May Not Work)

```bash
# WARNING: The system 'clojure' package is often the old REPL version
# This may not work for building Alethfeld
sudo apt update
sudo apt install clojure

# If this doesn't work, use Option 1 or 2 instead
```

### Verify Installation

```bash
# Check if clj command is available
clj --version

# Or check clojure CLI tools
clojure --version

# Test that -T flag works (for tooling)
clojure -Spath
```

If you get errors about `-T` or `-Spath` not being recognized, you need to install the CLI Tools using Option 1 or 2.

## Installing LaTeX

### Option 1: Minimal Installation (Recommended)

```bash
sudo apt update
sudo apt install texlive-latex-base texlive-latex-extra
```

This installs the base LaTeX system and common packages (amsmath, amssymb, amsthm, etc.).

### Option 2: Full TeX Live Distribution

```bash
sudo apt update
sudo apt install texlive-full
```

**Note**: This is a large installation (~4GB) but includes all packages.

### Verify Installation

```bash
pdflatex --version
```

## Building Alethfeld CLI

After installing Clojure, build the Alethfeld CLI:

```bash
cd /home/muntasir/Assembly/alethfeld/cli
clojure -T:build uber
```

This creates `target/alethfeld.jar` which is required for the CLI scripts.

## Testing the Installation

1. **Test Clojure**:
   ```bash
   clojure --version
   ```

2. **Test LaTeX**:
   ```bash
   cd examples/sum-degrees-even
   pdflatex sum-degrees-even.tex
   ```

3. **Test Alethfeld CLI**:
   ```bash
   cd cli
   ./scripts/alethfeld stats ../examples/sum-degrees-even/sum-degrees-even.edn
   ```

## Troubleshooting

### Clojure Issues

- If `clojure` command not found, ensure it's in your PATH
- Check `~/.bashrc` or `~/.zshrc` for PATH configuration
- Try `java -version` to ensure Java is installed (Clojure requires Java)

### LaTeX Issues

- If `pdflatex` not found, ensure texlive packages are installed
- Check `/usr/bin/pdflatex` exists
- For missing packages, install `texlive-latex-extra` or specific package

### Alethfeld CLI Issues

- Ensure `target/alethfeld.jar` exists (run `clojure -T:build uber`)
- Check script permissions: `chmod +x cli/scripts/alethfeld`
- Verify Java version compatibility (Java 11+ recommended)
