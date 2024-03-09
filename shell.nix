{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell.override {
  stdenv = pkgs.gccStdenv;
} {
  packages = with pkgs; [
    gdb cmake pkg-config meson ninja
    boost fmt clang-tools
  ];
  hardeningDisable = ["all"];
  shellHook = ''
    export CMAKE_EXPORT_COMPILE_COMMANDS=1
  '';
  buildInputs = [
    
  ];
}
