import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// When deploying to GitHub Pages under a repository path, set VITE_BASE=/StatPath/
export default defineConfig({
  plugins: [react()],
  base: process.env.VITE_BASE ?? "/",
  test: {
    environment: "node",
    include: ["tests/**/*.test.ts"],
  },
} as Parameters<typeof defineConfig>[0]);
