# Bend: the asynchronous scheduler and page I/O (patch)

This branch holds the change the browser TCP work needs in the Bend toolchain. The toolchain lives
in its own repository (bendlang/bend), so the change is kept here as a patch on its base commit.

- **Base:** bendlang/bend `9d514f3bb0d77524fcaa652645c902e4524eb838`.
- **Patch:** `0001-bend2-asynchronous-scheduler-and-page-io.patch` (one commit, touches `bend2/comp.ts`
  and `bend2/main.ts`).
- **Apply:** `sh patches/bend/apply.sh <dir>`. It clones bendlang/bend into `<dir>`, makes the branch
  `browser-async-scheduler` on the base, applies the patch, and prints `<dir>/bend2/main.ts`.

## What the patch changes

1. **An asynchronous scheduler.** A wait that no file descriptor backs (a WebSocket message, a host
   timer) parks with no fd and is woken by `io_notify`. A notice re-checks every external wait, one
   with a deadline too. The top-level run awaits; a nested run keeps the blocking poll.
2. **Host-neutral I/O.** The runtime names no Node or Bun module in its code. `io_node(name)` looks
   up `fs`, `tty` and `bun:ffi` when used, through `process.getBuiltinModule`. A page has none of
   them: its output goes to `#bend-output` (or `globalThis.bend_stdout`, or the console), and a
   system call throws.
3. **Page modules.** A module that a page imports carries the runtime's I/O and scheduler, and
   exports `page_main`, which runs the program's `main` through the scheduler. `main` is compiled
   into the module when the program has one.

## How it was checked

- The patch applies to bendlang/bend `9d514f3` (checked from a fresh clone with `apply.sh`).
- The patched toolchain runs a program that prints (`IO.print`), and the existing listen declaration
  (`browser/tests/decl_listen.bend`, prints 95).
- The browser tests (`bun test browser/test` in the StatPath repo, with `BEND_MAIN` set to the
  patched `bend2/main.ts`): the page programs under the runtime, and a page built with the Bend CLI
  and run in Chromium, whose output reaches the page.

## Status

Approved for use from this branch (the repository owner's decision, recorded in
`browser/DECISIONS.md` on `claude/adoring-tesla-vr51jc`). Not proposed upstream. The base commit is
not changed; the patch is the only difference.
