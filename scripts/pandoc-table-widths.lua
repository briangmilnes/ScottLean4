-- pandoc-table-widths.lua — set a table's column widths from what each column
-- actually holds: a floor from its longest unbreakable word, the rest shared in
-- proportion to its longest cell.
--
-- Why this exists: pandoc sizes pipe-table columns from the length of the dash
-- runs in the Markdown separator row, not from the cells. This project's tables
-- are written `| -- | ------ | ---- | ------ | -- |` — near equal — while the
-- content is wildly unequal: `PaperInventory.md`'s Progress table has a `Done`
-- column carrying 90-word paragraphs beside a `Remaining` column carrying an em
-- dash. Measured on the r0036 build, the prose column rendered about 1.4 inches
-- wide and one row filled a whole page.
--
-- Two failure modes, and the filter has to avoid both:
--
--   too narrow for the prose  — the original defect;
--   too narrow for a *word*   — the first version of this filter used a flat
--                               minimum fraction and produced `Un-num-bered`
--                               and `Mod-ules / lines / the-o-rems` down a
--                               half-inch column, and `SFP.lean` overprinting
--                               the next column, because an identifier has no
--                               hyphenation points and LaTeX lets it overflow.
--
-- So the floor is per column: its longest single word, which is what the column
-- must fit for nothing to overhang. Whatever width is left over after the floors
-- is shared in proportion to each column's longest cell — that is the part that
-- gives the prose its room.
--
-- Applied by scripts/md2pdf.sh to every conversion. A table whose columns are
-- already balanced comes out essentially unchanged, proportional allocation
-- being the identity on equal inputs.

-- Characters that fit across the text block at the body size md2pdf.sh sets.
-- Only the ratio matters, so this needs to be about right, not exact.
local LINE_CHARS = 92
local MAX_FRAC = 0.60   -- no column starves the others
local PAD = 1           -- breathing room beside the longest word

local function longest_word(s)
  local m = 0
  for w in s:gmatch("%S+") do
    if #w > m then m = #w end
  end
  return m
end

-- Per column: the longest cell (drives the proportional share) and the longest
-- single word (drives the floor). Maximum rather than sum, because a column's
-- width has to accommodate its widest entry; summing would let a column of many
-- short cells outweigh one holding a single long paragraph.
local function measure(tbl, ncols, widest, word)
  local function scan(rows)
    for _, row in ipairs(rows) do
      local col = 1
      for _, cell in ipairs(row.cells) do
        if col <= ncols then
          local s = pandoc.utils.stringify(cell)
          if #s > widest[col] then widest[col] = #s end
          local w = longest_word(s)
          if w > word[col] then word[col] = w end
          col = col + (cell.col_span or 1)
        end
      end
    end
  end
  scan(tbl.head.rows)
  for _, body in ipairs(tbl.bodies) do
    scan(body.body)
  end
end

function Table(tbl)
  local ncols = #tbl.colspecs
  if ncols == 0 then return nil end

  local widest, word = {}, {}
  for i = 1, ncols do widest[i], word[i] = 0, 0 end
  measure(tbl, ncols, widest, word)

  -- Floors, in fractions of the text width.
  local floor, floorsum = {}, 0
  for i = 1, ncols do
    floor[i] = (word[i] + PAD) / LINE_CHARS
    floorsum = floorsum + floor[i]
  end

  -- Pathological case: the floors alone overflow the line. Scale them to fit —
  -- something must overhang, and shrinking every column proportionally spreads
  -- the damage rather than concentrating it.
  if floorsum >= 0.95 then
    local k = 0.95 / floorsum
    for i = 1, ncols do floor[i] = floor[i] * k end
    floorsum = 0.95
  end

  local total = 0
  for i = 1, ncols do total = total + widest[i] end
  if total == 0 then return nil end

  -- Share what the floors leave, in proportion to the longest cell.
  local slack = 1.0 - floorsum
  local frac, sum = {}, 0
  for i = 1, ncols do
    local f = floor[i] + slack * (widest[i] / total)
    if f > MAX_FRAC then f = MAX_FRAC end
    frac[i] = f
    sum = sum + f
  end

  for i = 1, ncols do
    local align = tbl.colspecs[i][1]
    tbl.colspecs[i] = { align, frac[i] / sum }
  end
  return tbl
end
