// BPS patch applier and CRC32, written from the BPS format spec (byuu/near).
// The patch file holds only the bytes the hack changes; each player supplies
// their own Super Mario All-Stars ROM and this rebuilds the hack in the browser.
'use strict';

const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
    t[n] = c >>> 0;
  }
  return t;
})();

export function crc32(bytes, start = 0, end = bytes.length) {
  let c = 0xFFFFFFFF;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}

export function applyBps(source, patch) {
  const u32 = (a, o) => (a[o] | (a[o + 1] << 8) | (a[o + 2] << 16) | (a[o + 3] << 24)) >>> 0;
  if (patch.length < 16 || String.fromCharCode(...patch.subarray(0, 4)) !== 'BPS1')
    throw new Error('not a BPS patch');
  const end = patch.length - 12;
  if (crc32(patch, 0, patch.length - 4) !== u32(patch, patch.length - 4))
    throw new Error('the patch file is damaged (checksum mismatch)');

  let p = 4;
  const varint = () => {
    let data = 0, shift = 1;
    for (;;) {
      const x = patch[p++];
      data += (x & 0x7F) * shift;
      if (x & 0x80) break;
      shift *= 128;
      data += shift;
    }
    return data;
  };

  const srcSize = varint(), tgtSize = varint(), metaSize = varint();
  p += metaSize;
  if (source.length !== srcSize)
    throw new Error(`this ROM is ${source.length} bytes; the patch expects ${srcSize}`);
  if (crc32(source) !== u32(patch, end))
    throw new Error('this is not the Super Mario All-Stars (USA) ROM the patch was made from');

  const target = new Uint8Array(tgtSize);
  let out = 0, srcRel = 0, tgtRel = 0;
  while (p < end) {
    const d = varint();
    const cmd = d & 3, len = (d >>> 2) + 1;
    if (cmd === 0) {                       // SourceRead
      target.set(source.subarray(out, out + len), out); out += len;
    } else if (cmd === 1) {                // TargetRead
      target.set(patch.subarray(p, p + len), out); out += len; p += len;
    } else {
      const o = varint();
      const off = (o & 1 ? -1 : 1) * Math.floor(o / 2);
      if (cmd === 2) {                     // SourceCopy
        srcRel += off;
        target.set(source.subarray(srcRel, srcRel + len), out);
        srcRel += len; out += len;
      } else {                             // TargetCopy (may overlap itself)
        tgtRel += off;
        for (let i = 0; i < len; i++) target[out++] = target[tgtRel++];
      }
    }
  }
  if (crc32(target) !== u32(patch, end + 4))
    throw new Error('patched ROM failed its checksum');
  return target;
}

// Copier-dumped ROMs carry a 512-byte header the patch does not expect.
export function stripCopierHeader(rom) {
  return (rom.length % 1024 === 512) ? rom.subarray(512) : rom;
}
