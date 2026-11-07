#!/usr/bin/env node
// External WPT layout geometry check (Roadmap Phase 6):
// Launches headless Chromium via Playwright 1.63.0, measures DOM layout geometry
// (`offsetTop`, `offsetLeft`, `offsetWidth`, `offsetHeight`, `getClientRects()`) on
// CSS 2.1 block and inline formatting context fixtures, and compares every coordinate
// against the compiled Bend layout model (`docs/chromium-layout/layout.mjs`).

const assert = require("node:assert/strict");
const { existsSync } = require("node:fs");
const { join } = require("node:path");
const { pathToFileURL } = require("node:url");

const HEADLESS_SHELL_CANDIDATES = [
  process.env.CHROMIUM_EXECUTABLE_PATH,
  "/root/.cache/ms-playwright/chromium_headless_shell-1200/chrome-headless-shell-linux64/chrome-headless-shell",
  "/root/.cache/ms-playwright/chromium-1200/chrome-linux/chrome",
].filter(Boolean);

function findExecutable() {
  for (const p of HEADLESS_SHELL_CANDIDATES) {
    if (existsSync(p)) return p;
  }
  return undefined;
}

const list = (xs) => xs.reduceRight((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
const unList = (l) => {
  const xs = [];
  for (let x = l; x && x.$ === "Con"; x = x.tail) xs.push(x.head);
  return xs;
};
const strut = (is = 0, ie = 0, bs = 0, be = 0) => ({
  $: "Strut",
  inline_start: is,
  inline_end: ie,
  block_start: bs,
  block_end: be,
});
const mstrut = (pos = 0, neg = 0) => ({ $: "MStrut", pos, neg });
const fheight = (ascent = 0, descent = 0) => ({ $: "FHeight", ascent, descent });
const someNat = (val) => ({ $: "SomeNat", val });
const noneNat = () => ({ $: "NoneNat" });

async function main() {
  const layoutMod = await import(pathToFileURL(join(__dirname, "layout.mjs")).href);
  const layout = layoutMod.default;
  const { chromium } = require("playwright");
  const executablePath = findExecutable();
  const browser = await chromium.launch(executablePath ? { executablePath } : {});

  try {
    const page = await browser.newPage();

    // Case 1: BFC container with two in-flow block children and collapsing sibling margins
    await page.setContent(`
      <!doctype html>
      <style>
        body { margin: 0; padding: 0; }
        #bfc1 { position: relative; display: flow-root; width: 100px; }
        #c1 { width: 80px; height: 20px; margin: 10px 0 20px 5px; }
        #c2 { width: 90px; height: 25px; margin: 30px 0 40px 8px; }
      </style>
      <div id="bfc1"><div id="c1"></div><div id="c2"></div></div>
    `);
    const dom1 = await page.evaluate(() => {
      const b = document.getElementById("bfc1");
      const c1 = document.getElementById("c1");
      const c2 = document.getElementById("c2");
      return {
        bW: b.offsetWidth,
        bH: b.offsetHeight,
        c1: { left: c1.offsetLeft, top: c1.offsetTop, width: c1.offsetWidth, height: c1.offsetHeight },
        c2: { left: c2.offsetLeft, top: c2.offsetTop, width: c2.offsetWidth, height: c2.offsetHeight },
      };
    });

    const space1 = {
      $: "CSpace",
      available_inline_size: 200,
      available_block_size: noneNat(),
      bfc_line_offset: 0,
      bfc_block_offset: 0,
      margin_strut: mstrut(),
      is_new_bfc: false,
    };
    const node1 = {
      $: "BlockContainer",
      node_id: 1,
      border: strut(),
      padding: strut(),
      margin: strut(),
      explicit_inline_size: someNat(100),
      explicit_block_size: noneNat(),
      is_new_bfc: true,
      children: list([
        {
          $: "BlockChild",
          node_id: 11,
          border: strut(),
          padding: strut(),
          margin: strut(5, 0, 10, 20),
          explicit_inline_size: someNat(80),
          explicit_block_size: someNat(20),
          is_new_bfc: false,
          content_block_size: 20,
          has_inflow_content: true,
          inner_start_strut: mstrut(),
          inner_end_strut: mstrut(),
        },
        {
          $: "BlockChild",
          node_id: 12,
          border: strut(),
          padding: strut(),
          margin: strut(8, 0, 30, 40),
          explicit_inline_size: someNat(90),
          explicit_block_size: someNat(25),
          is_new_bfc: false,
          content_block_size: 25,
          has_inflow_content: true,
          inner_start_strut: mstrut(),
          inner_end_strut: mstrut(),
        },
      ]),
    };
    const res1 = layout.layout_block(space1, node1);
    const frags1 = unList(res1.fragment.children);
    assert.equal(dom1.bW, res1.fragment.border_box_size.inline_size, "Case 1 container width");
    assert.equal(dom1.bH, res1.fragment.border_box_size.block_size, "Case 1 container height");
    assert.deepEqual(
      dom1.c1,
      {
        left: frags1[0].offset.inline_offset,
        top: frags1[0].offset.block_offset,
        width: frags1[0].border_box_size.inline_size,
        height: frags1[0].border_box_size.block_size,
      },
      "Case 1 child 1 geometry",
    );
    assert.deepEqual(
      dom1.c2,
      {
        left: frags1[1].offset.inline_offset,
        top: frags1[1].offset.block_offset,
        width: frags1[1].border_box_size.inline_size,
        height: frags1[1].border_box_size.block_size,
      },
      "Case 1 child 2 geometry",
    );

    // Case 2: Container with padding, self-collapsing intermediate block, and auto-width child
    await page.setContent(`
      <!doctype html>
      <style>
        body { margin: 0; padding: 0; }
        #bfc2 { position: relative; display: flow-root; width: 120px; padding-top: 4px; padding-bottom: 6px; }
        #d1 { height: 30px; margin: 10px 10px 20px 10px; }
        #d2 { height: 0px; margin: 25px 0 15px 0; }
        #d3 { height: 40px; margin: 12px 5px 18px 15px; }
      </style>
      <div id="bfc2"><div id="d1"></div><div id="d2"></div><div id="d3"></div></div>
    `);
    const dom2 = await page.evaluate(() => {
      const b = document.getElementById("bfc2");
      const d1 = document.getElementById("d1");
      const d2 = document.getElementById("d2");
      const d3 = document.getElementById("d3");
      return {
        bW: b.offsetWidth,
        bH: b.offsetHeight,
        d1: { left: d1.offsetLeft, top: d1.offsetTop, width: d1.offsetWidth, height: d1.offsetHeight },
        d2Height: d2.offsetHeight,
        d3: { left: d3.offsetLeft, top: d3.offsetTop, width: d3.offsetWidth, height: d3.offsetHeight },
      };
    });
    const node2 = {
      $: "BlockContainer",
      node_id: 2,
      border: strut(),
      padding: strut(0, 0, 4, 6),
      margin: strut(),
      explicit_inline_size: someNat(120),
      explicit_block_size: noneNat(),
      is_new_bfc: true,
      children: list([
        {
          $: "BlockChild",
          node_id: 21,
          border: strut(),
          padding: strut(),
          margin: strut(10, 10, 10, 20),
          explicit_inline_size: noneNat(),
          explicit_block_size: someNat(30),
          is_new_bfc: false,
          content_block_size: 30,
          has_inflow_content: true,
          inner_start_strut: mstrut(),
          inner_end_strut: mstrut(),
        },
        {
          $: "BlockChild",
          node_id: 22,
          border: strut(),
          padding: strut(),
          margin: strut(0, 0, 25, 15),
          explicit_inline_size: noneNat(),
          explicit_block_size: noneNat(),
          is_new_bfc: false,
          content_block_size: 0,
          has_inflow_content: false,
          inner_start_strut: mstrut(),
          inner_end_strut: mstrut(),
        },
        {
          $: "BlockChild",
          node_id: 23,
          border: strut(),
          padding: strut(),
          margin: strut(15, 5, 12, 18),
          explicit_inline_size: noneNat(),
          explicit_block_size: someNat(40),
          is_new_bfc: false,
          content_block_size: 40,
          has_inflow_content: true,
          inner_start_strut: mstrut(),
          inner_end_strut: mstrut(),
        },
      ]),
    };
    const res2 = layout.layout_block(space1, node2);
    const frags2 = unList(res2.fragment.children);
    assert.equal(dom2.bW, res2.fragment.border_box_size.inline_size, "Case 2 container width");
    assert.equal(dom2.bH, res2.fragment.border_box_size.block_size, "Case 2 container height");
    assert.deepEqual(
      dom2.d1,
      {
        left: frags2[0].offset.inline_offset,
        top: frags2[0].offset.block_offset,
        width: frags2[0].border_box_size.inline_size,
        height: frags2[0].border_box_size.block_size,
      },
      "Case 2 child 1 geometry",
    );
    assert.equal(dom2.d2Height, frags2[1].border_box_size.block_size, "Case 2 self-collapsing child height");
    assert.deepEqual(
      dom2.d3,
      {
        left: frags2[2].offset.inline_offset,
        top: frags2[2].offset.block_offset,
        width: frags2[2].border_box_size.inline_size,
        height: frags2[2].border_box_size.block_size,
      },
      "Case 2 child 3 geometry",
    );

    // Case 3: Inline formatting context with getClientRects() and line wrapping
    // Two atomic inline boxes (w=45, h=14 and w=50, h=20) inside an 80px inline formatting context
    // wrap onto 2 lines: line 1 has height 14 (y=0..14), line 2 has height 20 (y=14..34).
    await page.setContent(`
      <!doctype html>
      <style>
        body { margin: 0; padding: 0; }
        #ifc { width: 80px; font-size: 0; line-height: 0; }
        .ib { display: inline-block; vertical-align: bottom; }
        #i1 { width: 45px; height: 14px; }
        #i2 { width: 50px; height: 20px; }
      </style>
      <div id="ifc"><span class="ib" id="i1"></span><wbr><span class="ib" id="i2"></span></div>
    `);
    const dom3 = await page.evaluate(() => {
      const ifc = document.getElementById("ifc");
      const r1 = document.getElementById("i1").getClientRects()[0];
      const r2 = document.getElementById("i2").getClientRects()[0];
      return {
        ifcH: ifc.offsetHeight,
        r1: { left: Math.round(r1.left), top: Math.round(r1.top), width: Math.round(r1.width), height: Math.round(r1.height) },
        r2: { left: Math.round(r2.left), top: Math.round(r2.top), width: Math.round(r2.width), height: Math.round(r2.height) },
      };
    });
    const inlineItems = list([
      { $: "AtomicInline", item_id: 1, inline_size: 45, block_size: 14, font_height: fheight(14, 0) },
      { $: "AtomicInline", item_id: 2, inline_size: 50, block_size: 20, font_height: fheight(20, 0) },
    ]);
    const stacked3 = layout.stack_line_boxes(layout.break_lines(80, inlineItems), fheight(0, 0), 0);
    const lines3 = unList(stacked3.lines);
    const p1 = unList(lines3[0].items)[0];
    const p2 = unList(lines3[1].items)[0];
    assert.equal(dom3.ifcH, stacked3.total_block_size, "Case 3 IFC total block size");
    assert.deepEqual(
      dom3.r1,
      { left: p1.inline_offset, top: lines3[0].bfc_offset.block_offset + p1.block_offset, width: p1.inline_size, height: p1.block_size },
      "Case 3 line 1 atomic inline rect",
    );
    assert.deepEqual(
      dom3.r2,
      { left: p2.inline_offset, top: lines3[1].bfc_offset.block_offset + p2.block_offset, width: p2.inline_size, height: p2.block_size },
      "Case 3 line 2 atomic inline rect",
    );

    console.log("OK: WPT layout geometry check passed (3 fixtures, offsetTop/offsetLeft/offsetWidth/offsetHeight/getClientRects match layout.mjs)");
  } finally {
    await browser.close();
  }
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
