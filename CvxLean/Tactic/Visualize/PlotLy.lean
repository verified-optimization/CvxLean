import ProofWidgets.Component.Basic
import ProofWidgets.Component.HtmlDisplay

-- cd lake-packages/proofwidgets/widget
-- npm install react-plotly.js plotly.js
-- npm install -D @types/react-plotly.js
-- Edit src/plotly.tsx
  -- import React from 'react';
  -- import Plot from 'react-plotly.js';
  -- import { DocumentPosition } from '@leanprover/infoview';

  -- interface PlotLyProps {
  --     z: number[][];
  -- }

  -- export default function(props: PlotLyProps & { pos: DocumentPosition }) {
  --     return <Plot
  --         data={[
  --           {
  --             z: props.z,
  --             type: 'surface',
  --           },
  --         ]}
  --         layout={ {width: 500, height: 500, title: '3D plot'} }
  --       />
  -- }
-- cd ..
-- lake build widgetJsAllDev

section Plotly

open Lean Widget ProofWidgets

structure PlotLyProps where 
  x : Array Float
  y : Array Float
  z : Array (Array (Option Float))
  deriving ToJson, FromJson, Inhabited

#mkrpcenc PlotLyProps

@[widget_module]
def PlotLyDisplay : Component PlotLyProps where
  javascript := include_str ".." / ".." / ".." / "lake-packages" / "proofwidgets" / "build" / "js" / "plotly.js"

-- open scoped Jsx in
-- partial def draw3DPlot : THtml :=
--   <PlotLyDisplay 
--     x={#[0,0.5,1].map some}
--     y={#[0,5,10].map some}
--     z={(#[#[0, 1, 2], #[3, 4, 5]].map (Array.map some)).push #[some 6, some 8, none] } />

-- #html draw3DPlot

end Plotly
