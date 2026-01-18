import { useMemo } from 'react';

type GoldenSpiralProps = {
  width?: number;
  height?: number;
  className?: string;
};

export function GoldenSpiral({ width = 400, height = 400, className }: GoldenSpiralProps) {
  const { spiralPath, rectangles } = useMemo(() => {
    // Fibonacci numbers for the spiral
    const fib = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    const totalSize = fib[fib.length - 1] + fib[fib.length - 2]; // 55 + 34 = 89
    const scale = (Math.min(width, height) * 0.85) / totalSize;

    // Build rectangles from small to large (Fibonacci tiling)
    // Each square is positioned relative to the growing rectangle
    const rects: { x: number; y: number; size: number }[] = [];

    // Start position for the smallest squares
    let rectX = 0;
    let rectY = 0;
    let rectW = fib[0] * scale;
    let rectH = fib[0] * scale;

    // First square
    rects.push({ x: rectX, y: rectY, size: fib[0] * scale });

    // Build up the tiling
    for (let i = 1; i < fib.length; i++) {
      const size = fib[i] * scale;
      const dir = i % 4;

      let newX: number, newY: number;

      switch (dir) {
        case 1: // Add to the right
          newX = rectX + rectW;
          newY = rectY + rectH - size;
          rectW += size;
          break;
        case 2: // Add below
          newX = rectX + rectW - size;
          newY = rectY + rectH;
          rectH += size;
          break;
        case 3: // Add to the left
          newX = rectX - size;
          newY = rectY;
          rectX = newX;
          rectW += size;
          break;
        case 0: // Add above
        default:
          newX = rectX;
          newY = rectY - size;
          rectY = newY;
          rectH += size;
          break;
      }

      rects.push({ x: newX, y: newY, size });
    }

    // Center the whole thing
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (const r of rects) {
      minX = Math.min(minX, r.x);
      minY = Math.min(minY, r.y);
      maxX = Math.max(maxX, r.x + r.size);
      maxY = Math.max(maxY, r.y + r.size);
    }

    const totalW = maxX - minX;
    const totalH = maxY - minY;
    const offsetX = (width - totalW) / 2 - minX;
    const offsetY = (height - totalH) / 2 - minY;

    for (const r of rects) {
      r.x += offsetX;
      r.y += offsetY;
    }

    // Generate spiral path
    // Spiral goes from center outward, connecting quarter circles
    let path = '';

    for (let i = 0; i < rects.length; i++) {
      const rect = rects[i];
      const r = rect.size;
      const dir = i % 4;

      // Determine arc center (the corner of the square where the arc pivots)
      let cx: number, cy: number;

      switch (dir) {
        case 0: // Arc pivots at bottom-right corner
          cx = rect.x + r;
          cy = rect.y + r;
          break;
        case 1: // Arc pivots at bottom-left corner
          cx = rect.x;
          cy = rect.y + r;
          break;
        case 2: // Arc pivots at top-left corner
          cx = rect.x;
          cy = rect.y;
          break;
        case 3: // Arc pivots at top-right corner
        default:
          cx = rect.x + r;
          cy = rect.y;
          break;
      }

      // Start and end angles for counter-clockwise spiral
      const baseAngle = ((dir + 2) % 4) * (Math.PI / 2);
      const startAngle = baseAngle;
      const endAngle = startAngle + Math.PI / 2;

      const startPtX = cx + r * Math.cos(startAngle);
      const startPtY = cy + r * Math.sin(startAngle);
      const endPtX = cx + r * Math.cos(endAngle);
      const endPtY = cy + r * Math.sin(endAngle);

      if (i === 0) {
        path += `M ${startPtX.toFixed(1)} ${startPtY.toFixed(1)}`;
      }

      // Add arc
      path += ` A ${r.toFixed(1)} ${r.toFixed(1)} 0 0 1 ${endPtX.toFixed(1)} ${endPtY.toFixed(1)}`;
    }

    return { spiralPath: path, rectangles: rects };
  }, [width, height]);

  return (
    <svg
      width={width}
      height={height}
      viewBox={`0 0 ${width} ${height}`}
      className={className}
      aria-hidden="true"
    >
      <defs>
        <linearGradient id="spiralGradient" x1="0%" y1="0%" x2="100%" y2="100%">
          <stop offset="0%" stopColor="rgba(255,255,255,0.15)" />
          <stop offset="100%" stopColor="rgba(255,255,255,0.5)" />
        </linearGradient>
      </defs>

      {rectangles.map((rect, i) => (
        <rect
          key={i}
          x={rect.x}
          y={rect.y}
          width={rect.size}
          height={rect.size}
          fill="none"
          stroke="rgba(255,255,255,0.08)"
          strokeWidth="1"
        />
      ))}

      <path
        d={spiralPath}
        fill="none"
        stroke="url(#spiralGradient)"
        strokeWidth="2"
        strokeLinecap="round"
      />
    </svg>
  );
}

export default GoldenSpiral;
