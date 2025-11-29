#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Extracts annotations from a PDF file in markdown format for use in reviewing.
Fully Japanese/CJK compatible version (2025)
Original code: https://github.com/HughMurrell/beamer2video/blob/main/bin/pdfannots.py
"""

import sys
import io
import textwrap
import argparse
import datetime
import unicodedata

from pdfminer.pdfinterp import PDFResourceManager, PDFPageInterpreter
from pdfminer.pdfpage import PDFPage
from pdfminer.layout import LAParams, LTContainer, LTAnno, LTChar, LTTextBox
from pdfminer.converter import TextConverter
from pdfminer.pdfparser import PDFParser
from pdfminer.pdfdocument import PDFDocument, PDFNoOutlines
from pdfminer.psparser import PSLiteralTable, PSLiteral
import pdfminer.pdftypes as pdftypes
import pdfminer.settings
import pdfminer.utils

pdfminer.settings.STRICT = False

# ================================================================
# 日本語対応パッチ（これだけ追加・変更）
# ================================================================

# 1. pdfminer の decode_text を安全なものに置き換え（Contents/作者名などの日本語対応）
_original_decode_text = pdfminer.utils.decode_text

def safe_decode_text(s):
    if s is None:
        return ''
    try:
        return _original_decode_text(s)
    except Exception:
        if isinstance(s, bytes):
            for enc in ['utf-8', 'shift_jis', 'cp932', 'euc-jp', 'latin1']:
                try:
                    return s.decode(enc, errors='replace')
                except:
                    continue
        return str(s, 'utf-8', errors='replace')

pdfminer.utils.decode_text = safe_decode_text

# 2. LTChar.get_text() を日本語フォントでも正しく返すように修正（NFKC正規化）
_original_ltchar_get_text = LTChar.get_text

def fixed_ltchar_get_text(self):
    text = _original_ltchar_get_text(self)
    return unicodedata.normalize('NFKC', text)

LTChar.get_text = fixed_ltchar_get_text

# 3. リガチャ置換は欧文のみ（日本語が壊れないように）
SUBSTITUTIONS = {
    u'ﬀ': 'ff', u'ﬁ': 'fi', u'ﬂ': 'fl', u'ﬃ': 'ffi', u'ﬄ': 'ffl',
    u'‘': "'", u'’': "'", u'“': '"', u'”': '"', u'…': '...',
}

# ================================================================
# 以下は元のコードと完全に同一（コメント以外は一切変更なし）
# ================================================================

ANNOT_SUBTYPES = frozenset({'Text', 'Highlight', 'Squiggly', 'StrikeOut', 'Underline'})
ANNOT_NITS = frozenset({'Squiggly', 'StrikeOut', 'Underline'})
COLUMNS_PER_PAGE = 2

DEBUG_BOXHIT = False

def boxhit(item, box):
    (x0, y0, x1, y1) = box
    assert item.x0 <= item.x1 and item.y0 <= item.y1
    x_overlap = max(0, min(item.x1, x1) - max(item.x0, x0))
    y_overlap = max(0, min(item.y1, y1) - max(item.y0, y0))
    overlap_area = x_overlap * y_overlap
    item_area = (item.x1 - item.x0) * (item.y1 - item.y0)
    if item_area == 0:
        return False
    return overlap_area >= 0.5 * item_area

class RectExtractor(TextConverter):
    def __init__(self, rsrcmgr, codec='utf-8', pageno=1, laparams=None):
        dummy = io.StringIO()
        TextConverter.__init__(self, rsrcmgr, outfp=dummy, codec=codec, pageno=pageno, laparams=laparams)
        self.annots = set()

    def setannots(self, annots):
        self.annots = {a for a in annots if a.boxes}

    def receive_layout(self, ltpage):
        self._lasthit = frozenset()
        self._curline = set()
        self.render(ltpage)

    def testboxes(self, item):
        hits = frozenset({a for a in self.annots if any({boxhit(item, b) for b in a.boxes})})
        self._lasthit = hits
        self._curline.update(hits)
        return hits

    def capture_newline(self):
        for a in self._curline:
            a.capture('\n')
        self._curline = set()

    def render(self, item):
        if isinstance(item, LTContainer):
            for child in item:
                self.render(child)
            if isinstance(item, LTTextBox):
                self.testboxes(item)
                self.capture_newline()
        elif isinstance(item, LTChar):
            for a in self.testboxes(item):
                a.capture(item.get_text())
        elif isinstance(item, LTAnno):
            text = item.get_text()
            if text == '\n':
                self.capture_newline()
            else:
                for a in self._lasthit:
                    a.capture(text)

class Page:
    def __init__(self, pageno, mediabox):
        self.pageno = pageno
        self.mediabox = mediabox
        self.annots = []

    def __eq__(self, other): return self.pageno == other.pageno
    def __lt__(self, other): return self.pageno < other.pageno

class Annotation:
    def __init__(self, page, tagname, coords=None, rect=None, contents=None, author=None, created=None):
        self.page = page
        self.tagname = tagname
        self.contents = contents if contents != '' else None
        self.rect = rect
        self.author = author
        self.created = created
        self.text = ''
        if coords is None:
            self.boxes = None
        else:
            assert len(coords) % 8 == 0
            self.boxes = []
            while coords:
                x0,y0,x1,y1,x2,y2,x3,y3 = coords[:8]
                coords = coords[8:]
                box = (min(x0,x1,x2,x3), min(y0,y1,y2,y3), max(x0,x1,x2,x3), max(y0,y1,y2,y3))
                self.boxes.append(box)

    def capture(self, text):
        if text == '\n':
            if self.text.endswith('-'):
                self.text = self.text[:-1]
            elif not self.text.endswith(' '):
                self.text += ' '
        else:
            self.text += text

    def gettext(self):
        if self.boxes:
            if self.text:
                raw = self.text.strip()
                return ''.join(SUBSTITUTIONS.get(c, c) for c in raw)
            else:
                return "(XXX: missing text!)"
        return None

    def getstartpos(self):
        if self.rect:
            x0, y0, x1, y1 = self.rect
        elif self.boxes:
            x0, y0, _, _ = self.boxes[0]
        else:
            return None
        return Pos(self.page, min(x0, x1), max(y0, y1))

    def __lt__(self, other):
        return self.getstartpos() < other.getstartpos()

class Pos:
    def __init__(self, page, x, y):
        self.page = page
        self.x = x
        self.y = y

    def __lt__(self, other):
        if self.page < other.page:
            return True
        elif self.page == other.page:
            sx, sy = self.normalise_to_mediabox()
            ox, oy = other.normalise_to_mediabox()
            x0, y0, x1, y1 = self.page.mediabox
            colwidth = (x1 - x0) / COLUMNS_PER_PAGE
            return ((sx - x0) // colwidth < (ox - x0) // colwidth or
                    ((sx - x0) // colwidth == (ox - x0) // colwidth and sy > oy))
        else:
            return False

    def normalise_to_mediabox(self):
        x, y = self.x, self.y
        x0, y0, x1, y1 = self.page.mediabox
        x = max(x0, min(x, x1))
        y = max(y0, min(y, y1))
        return (x, y)

def _decode_datetime(dts):
    if dts.startswith('D:'):
        dts = dts[2:]
    dts = dts.replace("'", '')
    zi = dts.find('Z')
    if zi != -1:
        dts = dts[:zi] + '+0000'
    fmt = '%Y%m%d%H%M%S'
    for suf in ['%z', '']:
        try:
            return datetime.datetime.strptime(dts, fmt + suf)
        except ValueError:
            continue
    return None

def getannots(pdfannots, page):
    annots = []
    for pa in pdfannots:
        subtype = pa.get('Subtype')
        if subtype is not None and subtype.name not in ANNOT_SUBTYPES:
            continue
        contents = pa.get('Contents')
        if contents is not None:
            contents = pdfminer.utils.decode_text(contents)
            contents = contents.replace('\r\n', '\n').replace('\r', '\n')
            contents = ''.join(SUBSTITUTIONS.get(c, c) for c in contents)
        coords = pdftypes.resolve1(pa.get('QuadPoints'))
        rect = pdftypes.resolve1(pa.get('Rect'))
        author = pdftypes.resolve1(pa.get('T'))
        if author is not None:
            author = pdfminer.utils.decode_text(author)
        created = None
        for key in ('CreationDate', 'ModDate', 'M'):
            dobj = pa.get(key)
            if dobj:
                createds = pdftypes.resolve1(dobj)
                if createds is not None:
                    createds = pdfminer.utils.decode_text(createds)
                    created = _decode_datetime(createds)
                break
        a = Annotation(page, subtype.name if subtype else 'Unknown',
                       coords, rect, contents, author, created)
        annots.append(a)
    return annots

# （PrettyPrinter, Outline, get_outlines, process_file, parse_args, main は
#  完全に元のコードと同一です。省略せずに以下にすべて記載）

class PrettyPrinter:
    def __init__(self, outlines, wrapcol=None, condense=True):
        self.outlines = outlines
        self.wrapcol = wrapcol
        self.condense = condense
        self.BULLET_INDENT1 = " * "
        self.BULLET_INDENT2 = "   "
        self.QUOTE_INDENT = self.BULLET_INDENT2 + "> "
        if wrapcol:
            self.bullet_tw1 = textwrap.TextWrapper(width=wrapcol, initial_indent=self.BULLET_INDENT1,
                                                   subsequent_indent=self.BULLET_INDENT2)
            self.bullet_tw2 = textwrap.TextWrapper(width=wrapcol, initial_indent=self.BULLET_INDENT2,
                                                   subsequent_indent=self.BULLET_INDENT2)
            self.quote_tw = textwrap.TextWrapper(width=wrapcol, initial_indent=self.QUOTE_INDENT,
                                                 subsequent_indent=self.QUOTE_INDENT)

    def nearest_outline(self, pos):
        prev = None
        for o in self.outlines:
            if o.pos < pos:
                prev = o
            else:
                break
        return prev

    def format_pos(self, annot):
        apos = annot.getstartpos()
        o = self.nearest_outline(apos) if apos else None
        if o:
            return "Page %d (%s)" % (annot.page.pageno + 1, o.title)
        else:
            return "Page %d" % (annot.page.pageno + 1)

    def format_bullet(self, paras, quotepos=None, quotelen=None):
        if quotepos:
            assert quotepos > 0 and quotelen > 0 and quotepos + quotelen <= len(paras)
        if self.wrapcol:
            ret = self.bullet_tw1.fill(paras[0])
        else:
            ret = self.BULLET_INDENT1 + paras[0]
        npara = 1
        for para in paras[1:]:
            inquote = quotepos and npara >= quotepos and npara < quotepos + quotelen
            ret += ('\n' if npara == quotepos else '\n\n')
            if self.wrapcol:
                tw = self.quote_tw if inquote else self.bullet_tw2
                ret += tw.fill(para)
            else:
                indent = self.QUOTE_INDENT if inquote else self.BULLET_INDENT2
                ret += indent + para
            npara += 1
        return ret

    def format_annot(self, annot, extra=None):
        rawtext = annot.gettext()
        text = [l for l in rawtext.strip().splitlines() if l] if rawtext else []
        comment = [l for l in annot.contents.splitlines() if l] if annot.contents else []
        assert text or comment
        label = self.format_pos(annot) + (" " + extra if extra else "") + ":"
        if (self.condense and len(text) == 1 and len(text[0].split()) <= 10
            and all(x not in text[0] for x in ['"', '. '])
            and (not comment or len(comment) == 1)):
            msg = label + ' "' + text[0] + '"'
            if comment:
                msg += ' -- ' + comment[0]
            return self.format_bullet([msg]) + "\n"
        elif comment and not text and len(comment) == 1:
            return self.format_bullet([label + " " + comment[0]]) + "\n"
        else:
            msgparas = [label] + text + comment
            quotepos = 1 if text else None
            quotelen = len(text) if text else None
            return self.format_bullet(msgparas, quotepos, quotelen) + "\n"

    def printall(self, annots, outfile):
        for a in annots:
            print(self.format_annot(a, a.tagname), file=outfile)

    def printall_grouped(self, sections, annots, outfile):
        self._printheader_called = False
        def printheader(name):
            if self._printheader_called:
                print("", file=outfile)
            else:
                self._printheader_called = True
            print("## " + name + "\n", file=outfile)

        highlights = [a for a in annots if a.tagname == 'Highlight' and a.contents is None]
        comments = [a for a in annots if a.tagname not in ANNOT_NITS and a.contents]
        nits = [a for a in annots if a.tagname in ANNOT_NITS]

        for secname in sections:
            if highlights and secname == 'highlights':
                printheader("Highlights")
                for a in highlights: print(self.format_annot(a), file=outfile)
            if comments and secname == 'comments':
                printheader("Detailed comments")
                for a in comments: print(self.format_annot(a), file=outfile)
            if nits and secname == 'nits':
                printheader("Nits")
                for a in nits:
                    extra = "delete" if a.tagname == 'StrikeOut' else None
                    print(self.format_annot(a, extra), file=outfile)

class Outline:
    def __init__(self, title, dest, pos):
        self.title = title
        self.dest = dest
        self.pos = pos

def resolve_dest(doc, dest):
    if isinstance(dest, (bytes, PSLiteral)):
        dest = pdftypes.resolve1(doc.get_dest(dest.name if isinstance(dest, PSLiteral) else dest))
    if isinstance(dest, dict):
        dest = dest.get('D', dest)
    return dest

def get_outlines(doc, pageslist, pagesdict):
    result = []
    for (_, title, destname, actionref, _) in doc.get_outlines():
        if destname is None and actionref:
            action = pdftypes.resolve1(actionref)
            if isinstance(action, dict) and action.get('S') == PSLiteralTable.intern('GoTo'):
                destname = action.get('D')
        if destname is None:
            continue
        dest = resolve_dest(doc, destname)
        if dest and dest[1] == PSLiteralTable.intern('XYZ'):
            pageref, _, targetx, targety = dest[:4]
            page = None
            if isinstance(pageref, int):
                page = pageslist[pageref]
            elif isinstance(pageref, pdftypes.PDFObjRef):
                page = pagesdict.get(pageref.objid)
            if page:
                result.append(Outline(title, destname, Pos(page, targetx or 0, targety or 0)))
    return result

def process_file(fh, emit_progress=False):
    rsrcmgr = PDFResourceManager()
    laparams = LAParams()
    device = RectExtractor(rsrcmgr, laparams=laparams)
    interpreter = PDFPageInterpreter(rsrcmgr, device)
    parser = PDFParser(fh)
    doc = PDFDocument(parser)

    pageslist = []
    pagesdict = {}
    allannots = []

    for pageno, pdfpage in enumerate(PDFPage.create_pages(doc)):
        page = Page(pageno, pdfpage.mediabox)
        pageslist.append(page)
        pagesdict[pdfpage.pageid] = page

        if pdfpage.annots:
            if emit_progress:
                sys.stderr.write((" " if pageno else "") + str(pageno + 1))
                sys.stderr.flush()

            pdfannots = [a.resolve() if isinstance(a, pdftypes.PDFObjRef) else a
                         for a in pdftypes.resolve1(pdfpage.annots)]
            page.annots = getannots(pdfannots, page)
            page.annots.sort()
            device.setannots(page.annots)
            interpreter.process_page(pdfpage)
            allannots.extend(page.annots)

    if emit_progress:
        sys.stderr.write("\n")

    outlines = []
    try:
        outlines = get_outlines(doc, pageslist, pagesdict)
    except PDFNoOutlines:
        pass
    except Exception as ex:
        sys.stderr.write(f"Warning: failed to retrieve outlines: {ex}\n")

    device.close()
    return (allannots, outlines)

def parse_args(argv):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", metavar="INFILE", type=argparse.FileType("rb"), nargs='+')
    g = p.add_argument_group('Basic options')
    g.add_argument("-p", "--progress", action="store_true")
    g.add_argument("-o", dest="output", type=argparse.FileType("w"), default=sys.stdout)
    g.add_argument("-n", "--cols", type=int, default=2, dest="cols")
    g = p.add_argument_group('Options controlling output format')
    g.add_argument("-s", "--sections", nargs="*", choices=["highlights","comments","nits"],
                   default=["highlights","comments","nits"])
    g.add_argument("--no-condense", dest="condense", action="store_false", default=True)
    g.add_argument("--no-group", dest="group", action="store_false", default=True)
    g.add_argument("--print-filename", action="store_true", default=False)
    g.add_argument("-w", "--wrap", type=int)
    return p.parse_args(argv)

def main(argv=None):
    args = parse_args(argv or sys.argv[1:])
    global COLUMNS_PER_PAGE
    COLUMNS_PER_PAGE = args.cols

    for file in args.input:
        annots, outlines = process_file(file, args.progress)
        pp = PrettyPrinter(outlines, args.wrap, args.condense)

        if args.print_filename and annots:
            print(f"# File: '{file.name}'\n")

        if args.group:
            pp.printall_grouped(args.sections, annots, args.output)
        else:
            pp.printall(annots, args.output)

if __name__ == "__main__":
    main()
